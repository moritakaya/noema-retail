/**
 * Noema Retail: Main Worker Entry Point
 * 
 * Cloudflare Workers のメインエントリーポイント。
 * リクエストルーティングと Durable Objects の管理を行う。
 * 
 * エンドポイント:
 * - /api/inventory/* : 在庫操作
 * - /api/sync/* : チャネル同期
 * - /webhook/stripe : Stripe Webhook
 * - /webhook/smaregi : スマレジ Webhook（将来）
 * - /cron/* : 定期実行
 */

import { InventoryAttractor } from './attractors/InventoryAttractor';
import { SmaregiAdapter, type SmaregiConfig } from './adapters/SmaregiAdapter';
import { RakutenAdapter, type RakutenConfig } from './adapters/RakutenAdapter';
import { YahooAdapter, type YahooConfig } from './adapters/YahooAdapter';
import { StripeAdapter, type StripeConfig } from './adapters/StripeAdapter';

// ============================================================================
// 型定義
// ============================================================================

export interface Env {
  // Durable Objects
  INVENTORY_ATTRACTOR: DurableObjectNamespace;
  
  // 環境変数（秘匿情報は Secrets で管理）
  // Stripe
  STRIPE_API_KEY: string;
  STRIPE_WEBHOOK_SECRET: string;
  
  // 楽天
  RAKUTEN_SHOP_URL: string;
  RAKUTEN_SERVICE_SECRET: string;
  RAKUTEN_LICENSE_KEY: string;
  RAKUTEN_LICENSE_EXPIRY: string;
  
  // Yahoo
  YAHOO_SELLER_ID: string;
  YAHOO_CLIENT_ID: string;
  YAHOO_CLIENT_SECRET: string;
  YAHOO_REFRESH_TOKEN: string;
  YAHOO_PUBLIC_KEY: string;
  YAHOO_PUBLIC_KEY_VERSION: string;
  YAHOO_PUBLIC_KEY_EXPIRY: string;
  
  // スマレジ
  SMAREGI_CONTRACT_ID: string;
  SMAREGI_CLIENT_ID: string;
  SMAREGI_CLIENT_SECRET: string;
  SMAREGI_ACCESS_TOKEN: string;
  SMAREGI_STORE_ID: string;
  
  // 商品マッピング（JSON）
  PRODUCT_MAPPING: string;
}

// ============================================================================
// Durable Objects エクスポート
// ============================================================================

export { InventoryAttractor };

// ============================================================================
// メインハンドラー
// ============================================================================

export default {
  async fetch(request: Request, env: Env, _ctx: ExecutionContext): Promise<Response> {
    const url = new URL(request.url);
    const path = url.pathname;

    try {
      // CORS 対応
      if (request.method === 'OPTIONS') {
        return handleCors();
      }

      // ルーティング
      if (path.startsWith('/api/inventory')) {
        return handleInventoryApi(request, env, path.slice('/api/inventory'.length));
      }

      if (path.startsWith('/api/sync')) {
        return handleSyncApi(request, env, path.slice('/api/sync'.length));
      }

      if (path === '/webhook/stripe') {
        return handleStripeWebhook(request, env);
      }

      if (path.startsWith('/cron')) {
        return handleCron(request, env, path.slice('/cron'.length));
      }

      // ヘルスチェック
      if (path === '/health') {
        return Response.json({ status: 'ok', timestamp: Date.now() });
      }

      return Response.json({ error: 'Not found' }, { status: 404 });
    } catch (error) {
      console.error('Worker error:', error);
      return Response.json(
        { error: error instanceof Error ? error.message : 'Internal error' },
        { status: 500 }
      );
    }
  },

  // 定期実行（Cron Triggers）
  async scheduled(event: ScheduledEvent, env: Env, ctx: ExecutionContext): Promise<void> {
    console.log(`Cron trigger: ${event.cron}`);

    // 5分ごとの同期
    if (event.cron === '*/5 * * * *') {
      ctx.waitUntil(syncAllChannels(env));
    }

    // 1時間ごとの完全同期
    if (event.cron === '0 * * * *') {
      ctx.waitUntil(fullSync(env));
    }
  },
};

// ============================================================================
// 在庫 API ハンドラー
// ============================================================================

async function handleInventoryApi(
  request: Request,
  env: Env,
  path: string
): Promise<Response> {
  // InventoryAttractor への委譲
  const id = env.INVENTORY_ATTRACTOR.idFromName('main');
  const stub = env.INVENTORY_ATTRACTOR.get(id);
  
  // パスを再構築
  const url = new URL(request.url);
  const newUrl = new URL(`http://internal/inventory${path}${url.search}`);
  
  const response = await stub.fetch(
    new Request(newUrl.toString(), {
      method: request.method,
      headers: request.headers,
      body: request.body,
    })
  );

  return addCorsHeaders(response);
}

// ============================================================================
// 同期 API ハンドラー
// ============================================================================

async function handleSyncApi(
  request: Request,
  env: Env,
  path: string
): Promise<Response> {
  // POST /api/sync/:channel/:productId - チャネル同期
  if (request.method === 'POST') {
    const parts = path.split('/').filter(p => p);
    if (parts.length === 2) {
      const [channel, productId] = parts;
      return syncProduct(env, channel, productId);
    }
  }

  // POST /api/sync/all/:productId - 全チャネル同期
  if (request.method === 'POST' && path.startsWith('/all/')) {
    const productId = path.slice('/all/'.length);
    return syncProductAllChannels(env, productId);
  }

  // GET /api/sync/status/:productId - 同期状態取得
  if (request.method === 'GET' && path.startsWith('/status/')) {
    const productId = path.slice('/status/'.length);
    const id = env.INVENTORY_ATTRACTOR.idFromName('main');
    const stub = env.INVENTORY_ATTRACTOR.get(id);
    
    const response = await stub.fetch(
      new Request(`http://internal/sync/${productId}`, { method: 'GET' })
    );
    return addCorsHeaders(response);
  }

  return Response.json({ error: 'Not found' }, { status: 404 });
}

// ============================================================================
// Stripe Webhook ハンドラー
// ============================================================================

async function handleStripeWebhook(
  request: Request,
  env: Env
): Promise<Response> {
  const signature = request.headers.get('stripe-signature');
  if (!signature) {
    return Response.json({ error: 'Missing signature' }, { status: 400 });
  }

  const payload = await request.text();
  
  const config: StripeConfig = {
    apiKey: env.STRIPE_API_KEY,
    webhookSecret: env.STRIPE_WEBHOOK_SECRET,
    productMapping: JSON.parse(env.PRODUCT_MAPPING || '[]'),
  };
  
  const adapter = new StripeAdapter(config);
  
  const id = env.INVENTORY_ATTRACTOR.idFromName('main');
  const stub = env.INVENTORY_ATTRACTOR.get(id);
  
  const result = await adapter.handleWebhook(payload, signature, stub);
  
  if (result.success) {
    return Response.json({ received: true, message: result.message });
  } else {
    return Response.json(
      { error: result.message },
      { status: 400 }
    );
  }
}

// ============================================================================
// Cron ハンドラー
// ============================================================================

async function handleCron(
  _request: Request,
  env: Env,
  path: string
): Promise<Response> {
  // 手動トリガー用（開発/デバッグ）
  if (path === '/sync') {
    await syncAllChannels(env);
    return Response.json({ status: 'Sync triggered' });
  }

  if (path === '/full-sync') {
    await fullSync(env);
    return Response.json({ status: 'Full sync triggered' });
  }

  return Response.json({ error: 'Unknown cron path' }, { status: 404 });
}

// ============================================================================
// 同期ロジック
// ============================================================================

async function syncProduct(
  env: Env,
  channel: string,
  productId: string
): Promise<Response> {
  const id = env.INVENTORY_ATTRACTOR.idFromName('main');
  const stub = env.INVENTORY_ATTRACTOR.get(id);

  let adapter: SmaregiAdapter | RakutenAdapter | YahooAdapter;
  
  switch (channel) {
    case 'smaregi':
      adapter = new SmaregiAdapter(getSmaregiConfig(env));
      break;
    case 'rakuten':
      adapter = new RakutenAdapter(getRakutenConfig(env));
      break;
    case 'yahoo':
      adapter = new YahooAdapter(getYahooConfig(env));
      break;
    default:
      return Response.json({ error: `Unknown channel: ${channel}` }, { status: 400 });
  }

  const result = await adapter.syncToNoema(productId, stub);
  return Response.json(result);
}

async function syncProductAllChannels(
  env: Env,
  productId: string
): Promise<Response> {
  const id = env.INVENTORY_ATTRACTOR.idFromName('main');
  const stub = env.INVENTORY_ATTRACTOR.get(id);

  const adapters = [
    new SmaregiAdapter(getSmaregiConfig(env)),
    new RakutenAdapter(getRakutenConfig(env)),
    new YahooAdapter(getYahooConfig(env)),
  ];

  const results = await Promise.all(
    adapters.map(adapter => adapter.syncToNoema(productId, stub))
  );

  return Response.json({ productId, results });
}

async function syncAllChannels(_env: Env): Promise<void> {
  console.log('Starting sync all channels...');

  // pending 状態の同期を取得して処理
  // TODO: 実装
  // const id = _env.INVENTORY_ATTRACTOR.idFromName('main');
  // const stub = _env.INVENTORY_ATTRACTOR.get(id);

  console.log('Sync all channels completed');
}

async function fullSync(_env: Env): Promise<void> {
  console.log('Starting full sync...');

  // 全チャネルから在庫を取得して Noema と照合
  // TODO: 実装（_envを使用）

  console.log('Full sync completed');
}

// ============================================================================
// 設定ヘルパー
// ============================================================================

function getSmaregiConfig(env: Env): SmaregiConfig {
  return {
    contractId: env.SMAREGI_CONTRACT_ID,
    clientId: env.SMAREGI_CLIENT_ID,
    clientSecret: env.SMAREGI_CLIENT_SECRET,
    accessToken: env.SMAREGI_ACCESS_TOKEN,
    refreshToken: '', // 必要に応じて追加
    storeId: env.SMAREGI_STORE_ID,
    apiBaseUrl: 'https://api.smaregi.dev',
  };
}

function getRakutenConfig(env: Env): RakutenConfig {
  return {
    shopUrl: env.RAKUTEN_SHOP_URL,
    serviceSecret: env.RAKUTEN_SERVICE_SECRET,
    licenseKey: env.RAKUTEN_LICENSE_KEY,
    licenseExpiry: parseInt(env.RAKUTEN_LICENSE_EXPIRY || '0'),
  };
}

function getYahooConfig(env: Env): YahooConfig {
  return {
    sellerId: env.YAHOO_SELLER_ID,
    clientId: env.YAHOO_CLIENT_ID,
    clientSecret: env.YAHOO_CLIENT_SECRET,
    refreshToken: env.YAHOO_REFRESH_TOKEN,
    publicKey: env.YAHOO_PUBLIC_KEY,
    publicKeyVersion: parseInt(env.YAHOO_PUBLIC_KEY_VERSION || '1'),
    publicKeyExpiry: parseInt(env.YAHOO_PUBLIC_KEY_EXPIRY || '0'),
  };
}

// ============================================================================
// CORS ヘルパー
// ============================================================================

function handleCors(): Response {
  return new Response(null, {
    headers: {
      'Access-Control-Allow-Origin': '*',
      'Access-Control-Allow-Methods': 'GET, POST, PUT, DELETE, OPTIONS',
      'Access-Control-Allow-Headers': 'Content-Type, Authorization',
      'Access-Control-Max-Age': '86400',
    },
  });
}

function addCorsHeaders(response: Response): Response {
  const newHeaders = new Headers(response.headers);
  newHeaders.set('Access-Control-Allow-Origin', '*');
  
  return new Response(response.body, {
    status: response.status,
    statusText: response.statusText,
    headers: newHeaders,
  });
}
