// Noema Retail: Cloudflare Workers Runtime Wrapper
//
// PureScript のコンパイル結果を Cloudflare Workers ランタイムに接続する。
// Durable Object クラスのエクスポートと、fetch/scheduled ハンドラーの登録を行う。

import { DurableObject } from 'cloudflare:workers';
import * as Main from '../../../output/Main/index.js';
import * as InventoryAttractorModule from '../../../output/Platform.Cloudflare.InventoryAttractor/index.js';

// InventoryAttractor Durable Object
export class InventoryAttractor extends DurableObject {
  constructor(ctx, env) {
    super(ctx, env);
    this.state = InventoryAttractorModule.createAttractor(ctx)();
    this.env = env;
  }

  async fetch(request) {
    try {
      const response = InventoryAttractorModule.handleFetch(this.state)(request)();
      return response;
    } catch (error) {
      console.error('InventoryAttractor fetch error:', error);
      return new Response(JSON.stringify({ error: error.message }), {
        status: 500,
        headers: { 'Content-Type': 'application/json' },
      });
    }
  }

  async alarm() {
    try {
      InventoryAttractorModule.handleAlarm(this.state)();
    } catch (error) {
      console.error('InventoryAttractor alarm error:', error);
    }
  }
}

// Worker fetch handler
export default {
  async fetch(request, env, ctx) {
    try {
      const url = new URL(request.url);
      const path = url.pathname.split('/').filter(s => s.length > 0);

      // Health check
      if (path.length === 0) {
        return new Response(JSON.stringify({
          status: 'ok',
          service: 'noema-retail',
          runtime: 'purescript',
        }), {
          headers: { 'Content-Type': 'application/json' },
        });
      }

      // API routes → InventoryAttractor
      if (path[0] === 'api') {
        const id = env.INVENTORY_ATTRACTOR.idFromName('main');
        const stub = env.INVENTORY_ATTRACTOR.get(id);

        // 内部 URL に変換
        const internalPath = path.slice(1).join('/');
        const internalUrl = `http://internal/${internalPath}`;
        const internalRequest = new Request(internalUrl, {
          method: request.method,
          headers: request.headers,
          body: request.body,
        });

        return stub.fetch(internalRequest);
      }

      // 404
      return new Response(JSON.stringify({ error: 'Not found' }), {
        status: 404,
        headers: { 'Content-Type': 'application/json' },
      });
    } catch (error) {
      console.error('Worker fetch error:', error);
      return new Response(JSON.stringify({ error: error.message }), {
        status: 500,
        headers: { 'Content-Type': 'application/json' },
      });
    }
  },

  // Scheduled handler (Cron Trigger)
  async scheduled(event, env, ctx) {
    console.log('Running scheduled sync...');
    // TODO: チャネル同期ロジック
  },
};
