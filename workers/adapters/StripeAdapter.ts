/**
 * Noema Retail: StripeAdapter
 *
 * Stripe決済との連携アダプター。
 * Stripe Webhook を受信し、決済完了時に在庫を調整。
 *
 * 圏論的解釈：
 * StripeAdapter は Stripe 圏（決済イベント）から Noema 圏への関手。
 * 決済イベントを在庫変動イベントに変換。
 *
 * 注意:
 * Stripeは決済プラットフォームであり、在庫管理機能を持たない。
 * 在庫管理は Noema 側で行い、Stripe からは注文通知のみ受信。
 */

import type {
  Channel,
  InventoryEvent,
  SyncResult
} from '../attractors/InventoryAttractor';

// ============================================================================
// 型定義
// ============================================================================

export interface StripeConfig {
  apiKey: string;                    // Stripe API Key (sk_xxx)
  webhookSecret: string;             // Webhook Secret (whsec_xxx)
  productMapping: ProductMapping[];  // Stripe商品ID → Noema商品ID マッピング
}

/** 商品マッピング */
export interface ProductMapping {
  stripeProductId: string;    // Stripe の Product ID
  stripePriceId?: string;     // Stripe の Price ID（オプション）
  noemaProductId: string;     // Noema の商品ID
  noemaLocationId?: string;   // Noema のロケーションID
}

/** Webhook処理結果 */
export interface WebhookResult {
  success: boolean;
  message: string;
  eventsProcessed?: number;
}

/** Stripe Webhookイベント */
export interface StripeWebhookEvent {
  id: string;
  type: string;
  data: {
    object: StripeCheckoutSession | StripePaymentIntent | unknown;
  };
  created: number;
}

/** Stripe Checkout Session */
export interface StripeCheckoutSession {
  id: string;
  object: 'checkout.session';
  payment_status: 'paid' | 'unpaid' | 'no_payment_required';
  status: 'complete' | 'expired' | 'open';
  customer: string | null;
  customer_email: string | null;
  line_items?: {
    data: StripeLineItem[];
  };
  metadata?: Record<string, string>;
}

/** Stripe Line Item */
export interface StripeLineItem {
  id: string;
  price: {
    id: string;
    product: string;
  };
  quantity: number;
  description?: string;
}

/** Stripe Payment Intent */
export interface StripePaymentIntent {
  id: string;
  object: 'payment_intent';
  status: string;
  amount: number;
  currency: string;
  metadata?: Record<string, string>;
}

/** Stripe Refund */
export interface StripeRefund {
  id: string;
  object: 'refund';
  payment_intent: string;
  amount: number;
  status: 'succeeded' | 'pending' | 'failed';
  metadata?: Record<string, string>;
}

// ============================================================================
// StripeAdapter
// ============================================================================

export class StripeAdapter {
  private config: StripeConfig;
  private channel: Channel = 'self_ec';

  private static readonly API_BASE_URL = 'https://api.stripe.com/v1';

  constructor(config: StripeConfig) {
    this.config = config;
  }

  // ==========================================================================
  // Webhook 署名検証
  // ==========================================================================

  /**
   * Stripe Webhook署名の検証
   *
   * Stripe-Signature ヘッダーの形式:
   * t=timestamp,v1=signature,v1=signature2,...
   */
  async verifyWebhookSignature(
    payload: string,
    signature: string
  ): Promise<boolean> {
    const elements = signature.split(',');
    const signatureMap: Record<string, string[]> = {};

    for (const element of elements) {
      const [key, value] = element.split('=');
      if (!signatureMap[key]) {
        signatureMap[key] = [];
      }
      signatureMap[key].push(value);
    }

    const timestamp = signatureMap['t']?.[0];
    const signatures = signatureMap['v1'] || [];

    if (!timestamp || signatures.length === 0) {
      return false;
    }

    // タイムスタンプの検証（5分以内）
    const timestampNum = parseInt(timestamp);
    const now = Math.floor(Date.now() / 1000);
    if (Math.abs(now - timestampNum) > 300) {
      return false;
    }

    // 署名の計算
    const signedPayload = `${timestamp}.${payload}`;
    const expectedSignature = await this.computeHmacSha256(
      signedPayload,
      this.config.webhookSecret
    );

    // いずれかの署名が一致すればOK
    return signatures.some(sig => this.secureCompare(sig, expectedSignature));
  }

  /**
   * HMAC-SHA256 計算（Web Crypto API使用）
   */
  private async computeHmacSha256(message: string, secret: string): Promise<string> {
    const encoder = new TextEncoder();
    const keyData = encoder.encode(secret);
    const messageData = encoder.encode(message);

    const key = await crypto.subtle.importKey(
      'raw',
      keyData,
      { name: 'HMAC', hash: 'SHA-256' },
      false,
      ['sign']
    );

    const signature = await crypto.subtle.sign('HMAC', key, messageData);
    const hashArray = Array.from(new Uint8Array(signature));
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
  }

  /**
   * タイミング攻撃対策の比較
   */
  private secureCompare(a: string, b: string): boolean {
    if (a.length !== b.length) {
      return false;
    }
    let result = 0;
    for (let i = 0; i < a.length; i++) {
      result |= a.charCodeAt(i) ^ b.charCodeAt(i);
    }
    return result === 0;
  }

  // ==========================================================================
  // Webhook ハンドラー
  // ==========================================================================

  /**
   * Webhook イベント処理
   */
  async handleWebhook(
    payload: string,
    signature: string,
    inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<WebhookResult> {
    // 署名検証
    const isValid = await this.verifyWebhookSignature(payload, signature);
    if (!isValid) {
      return {
        success: false,
        message: 'Invalid webhook signature',
      };
    }

    // イベントパース
    let event: StripeWebhookEvent;
    try {
      event = JSON.parse(payload) as StripeWebhookEvent;
    } catch {
      return {
        success: false,
        message: 'Invalid JSON payload',
      };
    }

    // イベントタイプに応じた処理
    switch (event.type) {
      case 'checkout.session.completed':
        return this.handleCheckoutCompleted(
          event.data.object as StripeCheckoutSession,
          inventoryAttractor
        );

      case 'payment_intent.succeeded':
        // Payment Intent成功時（Checkout以外の決済）
        return this.handlePaymentIntentSucceeded(
          event.data.object as StripePaymentIntent,
          inventoryAttractor
        );

      case 'charge.refunded':
        // 返金時は在庫を戻す
        return this.handleRefund(
          event.data.object as StripeRefund,
          inventoryAttractor
        );

      default:
        // 未対応のイベントは成功として扱う
        return {
          success: true,
          message: `Event type ${event.type} acknowledged but not processed`,
          eventsProcessed: 0,
        };
    }
  }

  /**
   * Checkout Session 完了時の処理
   */
  private async handleCheckoutCompleted(
    session: StripeCheckoutSession,
    inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<WebhookResult> {
    if (session.payment_status !== 'paid') {
      return {
        success: true,
        message: 'Payment not yet completed',
        eventsProcessed: 0,
      };
    }

    // Line Itemsが含まれていない場合はAPIから取得が必要
    // （Webhook設定で line_items を含めることを推奨）
    const lineItems = session.line_items?.data;
    if (!lineItems || lineItems.length === 0) {
      return {
        success: true,
        message: 'No line items in session (consider expanding line_items in webhook)',
        eventsProcessed: 0,
      };
    }

    const events = this.lineItemsToInventoryEvents(lineItems, session.id);
    let processed = 0;
    const errors: string[] = [];

    for (const event of events) {
      try {
        const response = await inventoryAttractor.fetch(
          new Request('http://internal/adjust', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
              productId: event.productId,
              locationId: event.locationId,
              delta: event.delta,
              eventType: event.eventType,
              channel: event.channel,
              referenceId: event.referenceId,
              metadata: event.metadata,
            }),
          })
        );

        if (response.ok) {
          processed++;
        } else {
          const errorText = await response.text();
          errors.push(`Failed to adjust inventory: ${errorText}`);
        }
      } catch (error) {
        errors.push(
          `Error processing line item: ${
            error instanceof Error ? error.message : 'Unknown error'
          }`
        );
      }
    }

    if (errors.length > 0) {
      return {
        success: false,
        message: `Processed ${processed}/${events.length} items. Errors: ${errors.join('; ')}`,
        eventsProcessed: processed,
      };
    }

    return {
      success: true,
      message: `Successfully processed ${processed} inventory adjustments`,
      eventsProcessed: processed,
    };
  }

  /**
   * Payment Intent 成功時の処理
   */
  private async handlePaymentIntentSucceeded(
    _paymentIntent: StripePaymentIntent,
    _inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<WebhookResult> {
    // Payment Intent単体では商品情報が含まれないため、
    // metadataに商品情報を含めるか、別途処理が必要
    // 通常はCheckout Sessionを使用することを推奨
    return {
      success: true,
      message: 'Payment intent acknowledged (use checkout.session.completed for inventory)',
      eventsProcessed: 0,
    };
  }

  /**
   * 返金時の処理
   */
  private async handleRefund(
    _refund: StripeRefund,
    _inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<WebhookResult> {
    // 返金時は在庫を戻す処理
    // 実装には元の注文情報の参照が必要
    // TODO: 返金に関連する注文を特定し、在庫を戻す
    return {
      success: true,
      message: 'Refund acknowledged (inventory restoration not implemented)',
      eventsProcessed: 0,
    };
  }

  /**
   * Line Items を InventoryEvent に変換
   */
  private lineItemsToInventoryEvents(
    lineItems: StripeLineItem[],
    sessionId: string
  ): InventoryEvent[] {
    const timestamp = Date.now();
    const events: InventoryEvent[] = [];

    for (const item of lineItems) {
      const mapping = this.findProductMapping(item.price.product, item.price.id);
      if (!mapping) {
        console.warn(`No mapping found for Stripe product: ${item.price.product}`);
        continue;
      }

      events.push({
        eventType: 'sale' as const,
        productId: mapping.noemaProductId,
        locationId: mapping.noemaLocationId || 'self_ec_warehouse',
        channel: this.channel,
        delta: -item.quantity,
        referenceId: sessionId,
        timestamp,
        metadata: {
          stripeProductId: item.price.product,
          stripePriceId: item.price.id,
          description: item.description,
        },
      });
    }

    return events;
  }

  /**
   * 商品マッピングを検索
   */
  private findProductMapping(
    stripeProductId: string,
    stripePriceId?: string
  ): ProductMapping | null {
    // まずPrice IDで検索（より具体的）
    if (stripePriceId) {
      const byPrice = this.config.productMapping.find(
        m => m.stripePriceId === stripePriceId
      );
      if (byPrice) return byPrice;
    }

    // Product IDで検索
    return this.config.productMapping.find(
      m => m.stripeProductId === stripeProductId
    ) || null;
  }

  // ==========================================================================
  // Stripe API 呼び出し
  // ==========================================================================

  /**
   * Stripe API リクエスト
   */
  private async apiRequest<T>(
    method: 'GET' | 'POST',
    endpoint: string,
    params?: Record<string, string | number>
  ): Promise<T> {
    const url = `${StripeAdapter.API_BASE_URL}${endpoint}`;

    const headers: Record<string, string> = {
      'Authorization': `Bearer ${this.config.apiKey}`,
      'Content-Type': 'application/x-www-form-urlencoded',
    };

    let requestInit: RequestInit;

    if (method === 'GET') {
      const queryParams = new URLSearchParams();
      if (params) {
        for (const [key, value] of Object.entries(params)) {
          queryParams.set(key, String(value));
        }
      }
      const fullUrl = queryParams.toString() ? `${url}?${queryParams}` : url;
      requestInit = { method, headers };
      const response = await fetch(fullUrl, requestInit);
      return this.handleApiResponse<T>(response, endpoint);
    } else {
      const body = new URLSearchParams();
      if (params) {
        for (const [key, value] of Object.entries(params)) {
          body.set(key, String(value));
        }
      }
      requestInit = { method, headers, body: body.toString() };
      const response = await fetch(url, requestInit);
      return this.handleApiResponse<T>(response, endpoint);
    }
  }

  /**
   * APIレスポンス処理
   */
  private async handleApiResponse<T>(response: Response, endpoint: string): Promise<T> {
    if (!response.ok) {
      const errorText = await response.text();
      throw new StripeApiError(
        response.status,
        `Stripe API error: ${response.status} ${errorText}`,
        endpoint
      );
    }
    return response.json() as Promise<T>;
  }

  /**
   * Checkout Session の Line Items 取得
   */
  async getCheckoutSessionLineItems(sessionId: string): Promise<StripeLineItem[]> {
    interface LineItemsResponse {
      data: StripeLineItem[];
    }
    const response = await this.apiRequest<LineItemsResponse>(
      'GET',
      `/checkout/sessions/${sessionId}/line_items`
    );
    return response.data;
  }

  // ==========================================================================
  // Noema 連携（他アダプターとのインターフェース互換）
  // ==========================================================================

  /**
   * Stripe → Noema 同期
   *
   * 注意: Stripeは在庫管理機能を持たないため、
   * このメソッドは常に成功を返す（在庫情報は存在しない）
   */
  async syncToNoema(
    _productId: string,
    _inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<SyncResult> {
    return {
      success: true,
      channel: this.channel,
      timestamp: Date.now(),
      // Stripeには在庫概念がないため、quantitySyncedは返さない
    };
  }

  /**
   * Noema → Stripe 同期
   *
   * 注意: Stripeは在庫管理機能を持たないため、
   * このメソッドは何もしない
   */
  async syncFromNoema(
    _productId: string,
    _noemaQuantity: number
  ): Promise<SyncResult> {
    return {
      success: true,
      channel: this.channel,
      timestamp: Date.now(),
      // Stripeには在庫を設定する機能がない
    };
  }

  /**
   * 新しい注文を処理（ポーリング用）
   *
   * 注意: Stripeは通常Webhookで注文を受信するため、
   * このメソッドはフォールバック用
   */
  async processNewOrders(
    since: Date,
    inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<{ processed: number; errors: string[] }> {
    const errors: string[] = [];
    let processed = 0;

    try {
      // 完了したCheckout Sessionを取得
      interface SessionsResponse {
        data: StripeCheckoutSession[];
      }
      const response = await this.apiRequest<SessionsResponse>(
        'GET',
        '/checkout/sessions',
        {
          'created[gte]': Math.floor(since.getTime() / 1000),
          status: 'complete',
          limit: 100,
        }
      );

      for (const session of response.data) {
        if (session.payment_status !== 'paid') continue;

        // Line Itemsを取得
        const lineItems = await this.getCheckoutSessionLineItems(session.id);
        const events = this.lineItemsToInventoryEvents(lineItems, session.id);

        for (const event of events) {
          try {
            const res = await inventoryAttractor.fetch(
              new Request('http://internal/adjust', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                  productId: event.productId,
                  locationId: event.locationId,
                  delta: event.delta,
                  eventType: event.eventType,
                  channel: event.channel,
                  referenceId: event.referenceId,
                  metadata: event.metadata,
                }),
              })
            );

            if (res.ok) {
              processed++;
            } else {
              const errorText = await res.text();
              errors.push(`Failed to process session ${session.id}: ${errorText}`);
            }
          } catch (error) {
            errors.push(
              `Error processing session ${session.id}: ${
                error instanceof Error ? error.message : 'Unknown error'
              }`
            );
          }
        }
      }
    } catch (error) {
      errors.push(
        `Failed to fetch sessions: ${
          error instanceof Error ? error.message : 'Unknown error'
        }`
      );
    }

    return { processed, errors };
  }
}

// ============================================================================
// エラークラス
// ============================================================================

export class StripeApiError extends Error {
  statusCode: number;
  endpoint: string;

  constructor(statusCode: number, message: string, endpoint: string) {
    super(message);
    this.name = 'StripeApiError';
    this.statusCode = statusCode;
    this.endpoint = endpoint;
  }

  /**
   * リトライ可能なエラーかどうか
   */
  isRetryable(): boolean {
    return this.statusCode >= 500 || this.statusCode === 429;
  }
}
