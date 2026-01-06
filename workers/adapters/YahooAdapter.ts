/**
 * Noema Retail: YahooAdapter
 *
 * Yahoo!ショッピング（ストアクリエイターPro）との連携アダプター。
 * Yahoo!ショッピング ストアAPIを使用。
 *
 * 圏論的解釈：
 * YahooAdapter は Yahoo 圏から Noema 圏への関手。
 * Yahoo固有のデータ形式を Noema の統一形式に変換。
 *
 * 参考:
 * - https://developer.yahoo.co.jp/webapi/shopping/getStock.html
 * - https://developer.yahoo.co.jp/webapi/shopping/setStock.html
 */

import type {
  Channel,
  InventoryEvent,
  SyncResult
} from '../attractors/InventoryAttractor';

// ============================================================================
// 型定義
// ============================================================================

export interface YahooConfig {
  sellerId: string;             // ストアアカウント
  clientId: string;             // Client ID（アプリケーションID）
  clientSecret: string;         // シークレット
  refreshToken: string;         // リフレッシュトークン
  publicKey: string;            // 公開鍵（Webhook検証用）
  publicKeyVersion: number;     // 公開鍵バージョン
  publicKeyExpiry: number;      // 公開鍵有効期限（UNIX timestamp）
}

/** アクセストークンレスポンス */
interface TokenResponse {
  access_token: string;
  token_type: string;
  expires_in: number;
  refresh_token?: string;
}

/** 在庫参照APIレスポンス */
export interface YahooStockResponse {
  ResultSet: {
    totalResultsAvailable: number;
    totalResultsReturned: number;
    firstResultPosition: number;
    Result: YahooStockItem[];
  };
}

export interface YahooStockItem {
  ItemCode: string;             // 商品コード
  SubCode?: string;             // サブコード（SKU）
  Quantity: number;             // 在庫数
  AllowOverdraft?: number;      // マイナス在庫許可
}

/** 在庫更新APIリクエスト */
export interface YahooStockUpdateItem {
  item_code: string;
  sub_code?: string;
  quantity: number;
  allow_overdraft?: number;
}

/** 在庫更新APIレスポンス */
export interface YahooStockUpdateResponse {
  ResultSet: {
    Status: string;
    Result: {
      ItemCode: string;
      SubCode?: string;
      Quantity: number;
    }[];
  };
}

/** 注文検索APIレスポンス */
export interface YahooOrderSearchResponse {
  ResultSet: {
    totalResultsAvailable: number;
    totalResultsReturned: number;
    Result: {
      OrderId: string;
    }[];
  };
}

/** 注文詳細 */
export interface YahooOrder {
  OrderId: string;
  OrderTime: string;
  OrderStatus: string;
  Item: YahooOrderItem[];
}

export interface YahooOrderItem {
  ItemId: string;
  Title: string;
  SubCode?: string;
  Quantity: number;
  UnitPrice: number;
}

export interface YahooOrderDetailResponse {
  ResultSet: {
    Result: YahooOrder;
  };
}

// ============================================================================
// YahooAdapter
// ============================================================================

export class YahooAdapter {
  private config: YahooConfig;
  private channel: Channel = 'yahoo';
  private accessToken: string | null = null;
  private tokenExpiresAt = 0;

  private static readonly API_BASE_URL = 'https://circus.shopping.yahooapis.jp';
  private static readonly AUTH_URL = 'https://auth.login.yahoo.co.jp/yconnect/v2/token';

  constructor(config: YahooConfig) {
    this.config = config;
  }

  // ==========================================================================
  // OAuth2 認証
  // ==========================================================================

  /**
   * アクセストークン取得（リフレッシュトークン使用）
   */
  private async getAccessToken(): Promise<string> {
    // キャッシュされたトークンが有効な場合はそれを返す
    if (this.accessToken && Date.now() < this.tokenExpiresAt - 60000) {
      return this.accessToken;
    }

    const params = new URLSearchParams({
      grant_type: 'refresh_token',
      client_id: this.config.clientId,
      client_secret: this.config.clientSecret,
      refresh_token: this.config.refreshToken,
    });

    const response = await fetch(YahooAdapter.AUTH_URL, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/x-www-form-urlencoded',
      },
      body: params.toString(),
    });

    if (!response.ok) {
      const errorText = await response.text();
      throw new YahooApiError(
        response.status,
        `Yahoo OAuth error: ${response.status} ${errorText}`,
        'token'
      );
    }

    const tokenData = await response.json() as TokenResponse;
    this.accessToken = tokenData.access_token;
    this.tokenExpiresAt = Date.now() + tokenData.expires_in * 1000;

    return this.accessToken;
  }

  /**
   * API リクエストの共通処理
   */
  private async apiRequest<T>(
    method: 'GET' | 'POST',
    endpoint: string,
    params?: Record<string, string | number | undefined>
  ): Promise<T> {
    const token = await this.getAccessToken();
    const url = `${YahooAdapter.API_BASE_URL}${endpoint}`;

    const headers: Record<string, string> = {
      'Authorization': `Bearer ${token}`,
    };

    let requestInit: RequestInit;

    if (method === 'GET') {
      const queryParams = new URLSearchParams();
      if (params) {
        for (const [key, value] of Object.entries(params)) {
          if (value !== undefined) {
            queryParams.set(key, String(value));
          }
        }
      }
      const fullUrl = queryParams.toString() ? `${url}?${queryParams}` : url;
      requestInit = { method, headers };
      const response = await fetch(fullUrl, requestInit);
      return this.handleResponse<T>(response, endpoint);
    } else {
      headers['Content-Type'] = 'application/x-www-form-urlencoded';
      const body = new URLSearchParams();
      if (params) {
        for (const [key, value] of Object.entries(params)) {
          if (value !== undefined) {
            body.set(key, String(value));
          }
        }
      }
      requestInit = { method, headers, body: body.toString() };
      const response = await fetch(url, requestInit);
      return this.handleResponse<T>(response, endpoint);
    }
  }

  /**
   * レスポンス処理
   */
  private async handleResponse<T>(response: Response, endpoint: string): Promise<T> {
    if (!response.ok) {
      const errorText = await response.text();
      throw new YahooApiError(
        response.status,
        `Yahoo API error: ${response.status} ${errorText}`,
        endpoint
      );
    }

    const contentType = response.headers.get('content-type') || '';
    if (contentType.includes('application/json')) {
      return response.json() as Promise<T>;
    }
    // XMLの場合は簡易パース（本番ではxml2jsなどを使用）
    const text = await response.text();
    return this.parseXmlResponse<T>(text);
  }

  /**
   * XMLレスポンスの簡易パース
   *
   * 注意: 本番環境では適切なXMLパーサーを使用すべき
   */
  private parseXmlResponse<T>(xml: string): T {
    // 簡易的なXML→JSON変換（基本的な構造のみ対応）
    // Yahoo APIはJSONレスポンスも対応しているため、
    // outputパラメータでjsonを指定することを推奨
    const result: Record<string, unknown> = {};

    // ResultSet内のQuantity等を抽出
    const quantityMatch = xml.match(/<Quantity>(\d+)<\/Quantity>/);
    if (quantityMatch) {
      result.quantity = parseInt(quantityMatch[1]);
    }

    const itemCodeMatch = xml.match(/<ItemCode>([^<]+)<\/ItemCode>/);
    if (itemCodeMatch) {
      result.itemCode = itemCodeMatch[1];
    }

    const statusMatch = xml.match(/<Status>([^<]+)<\/Status>/);
    if (statusMatch) {
      result.status = statusMatch[1];
    }

    return result as T;
  }

  // ==========================================================================
  // 在庫操作
  // ==========================================================================

  /**
   * 在庫取得（単一商品）
   *
   * productId は "itemCode:subCode" 形式を想定
   */
  async getStock(productId: string): Promise<YahooStockItem | null> {
    const [itemCode, subCode] = this.parseProductId(productId);

    try {
      const params: Record<string, string | number | undefined> = {
        seller_id: this.config.sellerId,
        item_code: itemCode,
        output: 'json',
      };
      if (subCode && subCode !== 'default') {
        params.sub_code = subCode;
      }

      const response = await this.apiRequest<YahooStockResponse>(
        'POST',
        '/ShoppingWebService/V1/getStock',
        params
      );

      const items = response?.ResultSet?.Result;
      if (!items || items.length === 0) {
        return null;
      }

      return items[0];
    } catch (error) {
      if (error instanceof YahooApiError && error.statusCode === 404) {
        return null;
      }
      throw error;
    }
  }

  /**
   * 在庫一括取得
   */
  async getStocks(itemCodes: string[]): Promise<YahooStockItem[]> {
    const allItems: YahooStockItem[] = [];

    // Yahoo APIは一度に複数商品の在庫を取得できないため、
    // 個別にリクエスト（レート制限に注意）
    for (const itemCode of itemCodes) {
      const item = await this.getStock(itemCode);
      if (item) {
        allItems.push(item);
      }
      // レート制限対策（1リクエスト/秒）
      await this.sleep(1000);
    }

    return allItems;
  }

  /**
   * 在庫更新
   */
  async setStock(
    productId: string,
    quantity: number
  ): Promise<void> {
    const [itemCode, subCode] = this.parseProductId(productId);

    const params: Record<string, string | number | undefined> = {
      seller_id: this.config.sellerId,
      item_code: itemCode,
      quantity,
      output: 'json',
    };
    if (subCode && subCode !== 'default') {
      params.sub_code = subCode;
    }

    await this.apiRequest<YahooStockUpdateResponse>(
      'POST',
      '/ShoppingWebService/V1/setStock',
      params
    );
  }

  /**
   * 在庫調整
   *
   * SmaregiAdapter/RakutenAdapter と同じインターフェース。
   */
  async adjustStock(
    productId: string,
    delta: number,
    _reason: string
  ): Promise<void> {
    const current = await this.getStock(productId);
    if (!current) {
      throw new YahooApiError(404, `Product not found: ${productId}`, 'adjustStock');
    }

    const newQuantity = current.Quantity + delta;
    if (newQuantity < 0) {
      throw new Error(`Insufficient stock: current=${current.Quantity}, delta=${delta}`);
    }

    await this.setStock(productId, newQuantity);
  }

  // ==========================================================================
  // 注文操作
  // ==========================================================================

  /**
   * 注文検索
   */
  async searchOrders(params: {
    from: Date;
    to: Date;
    page?: number;
  }): Promise<string[]> {
    const response = await this.apiRequest<YahooOrderSearchResponse>(
      'POST',
      '/ShoppingWebService/V1/orderList',
      {
        seller_id: this.config.sellerId,
        start_date: this.formatDate(params.from),
        end_date: this.formatDate(params.to),
        start: ((params.page || 1) - 1) * 100 + 1,
        results: 100,
        output: 'json',
      }
    );

    return (response?.ResultSet?.Result || []).map(r => r.OrderId);
  }

  /**
   * 注文詳細取得
   */
  async getOrder(orderId: string): Promise<YahooOrder | null> {
    try {
      const response = await this.apiRequest<YahooOrderDetailResponse>(
        'POST',
        '/ShoppingWebService/V1/orderInfo',
        {
          seller_id: this.config.sellerId,
          order_id: orderId,
          output: 'json',
        }
      );

      return response?.ResultSet?.Result || null;
    } catch (error) {
      if (error instanceof YahooApiError && error.statusCode === 404) {
        return null;
      }
      throw error;
    }
  }

  /**
   * 注文を Noema の InventoryEvent に変換
   */
  orderToInventoryEvents(order: YahooOrder): InventoryEvent[] {
    const timestamp = new Date(order.OrderTime).getTime();
    const events: InventoryEvent[] = [];

    for (const item of order.Item || []) {
      const subCode = item.SubCode || 'default';
      events.push({
        eventType: 'sale' as const,
        productId: `${item.ItemId}:${subCode}`,
        locationId: `yahoo_${this.config.sellerId}`,
        channel: this.channel,
        delta: -item.Quantity,
        referenceId: order.OrderId,
        timestamp,
        metadata: {
          title: item.Title,
          unitPrice: item.UnitPrice,
        },
      });
    }

    return events;
  }

  // ==========================================================================
  // Noema 連携
  // ==========================================================================

  /**
   * Yahoo の在庫を Noema に同期
   */
  async syncToNoema(
    productId: string,
    inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<SyncResult> {
    const timestamp = Date.now();

    try {
      const yahooStock = await this.getStock(productId);

      if (!yahooStock) {
        return {
          success: false,
          channel: this.channel,
          error: `Product not found in Yahoo: ${productId}`,
          timestamp,
        };
      }

      const response = await inventoryAttractor.fetch(
        new Request('http://internal/sync', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            productId,
            channel: this.channel,
            remoteQuantity: yahooStock.Quantity,
          }),
        })
      );

      if (!response.ok) {
        const error = await response.text();
        return {
          success: false,
          channel: this.channel,
          error: `Noema sync failed: ${error}`,
          timestamp,
        };
      }

      return {
        success: true,
        channel: this.channel,
        quantitySynced: yahooStock.Quantity,
        timestamp,
      };
    } catch (error) {
      return {
        success: false,
        channel: this.channel,
        error: error instanceof Error ? error.message : 'Unknown error',
        timestamp,
      };
    }
  }

  /**
   * Noema の在庫を Yahoo に同期
   */
  async syncFromNoema(
    productId: string,
    noemaQuantity: number
  ): Promise<SyncResult> {
    const timestamp = Date.now();

    try {
      await this.setStock(productId, noemaQuantity);

      return {
        success: true,
        channel: this.channel,
        quantitySynced: noemaQuantity,
        timestamp,
      };
    } catch (error) {
      return {
        success: false,
        channel: this.channel,
        error: error instanceof Error ? error.message : 'Unknown error',
        timestamp,
      };
    }
  }

  /**
   * 新しい注文を Noema に反映
   */
  async processNewOrders(
    since: Date,
    inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<{ processed: number; errors: string[] }> {
    const errors: string[] = [];
    let processed = 0;

    try {
      const orderIds = await this.searchOrders({
        from: since,
        to: new Date(),
      });

      if (orderIds.length === 0) {
        return { processed: 0, errors: [] };
      }

      for (const orderId of orderIds) {
        try {
          const order = await this.getOrder(orderId);
          if (!order) continue;

          const events = this.orderToInventoryEvents(order);

          for (const event of events) {
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
              errors.push(`Failed to process event: ${errorText}`);
            }
          }

          // レート制限対策
          await this.sleep(1000);
        } catch (error) {
          errors.push(
            `Error processing order ${orderId}: ${
              error instanceof Error ? error.message : 'Unknown error'
            }`
          );
        }
      }
    } catch (error) {
      errors.push(
        `Failed to fetch orders: ${
          error instanceof Error ? error.message : 'Unknown error'
        }`
      );
    }

    return { processed, errors };
  }

  // ==========================================================================
  // ユーティリティ
  // ==========================================================================

  /**
   * productId を itemCode と subCode に分解
   * 形式: "itemCode:subCode"
   */
  private parseProductId(productId: string): [string, string] {
    const parts = productId.split(':');
    if (parts.length < 2) {
      return [productId, 'default'];
    }
    return [parts[0], parts.slice(1).join(':')];
  }

  /**
   * Yahoo API用の日付フォーマット（YYYYMMDD）
   */
  private formatDate(date: Date): string {
    const year = date.getFullYear();
    const month = String(date.getMonth() + 1).padStart(2, '0');
    const day = String(date.getDate()).padStart(2, '0');
    return `${year}${month}${day}`;
  }

  /**
   * スリープ（レート制限対策）
   */
  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  /**
   * 公開鍵有効期限チェック
   */
  isPublicKeyExpired(): boolean {
    return Date.now() >= this.config.publicKeyExpiry;
  }
}

// ============================================================================
// エラークラス
// ============================================================================

export class YahooApiError extends Error {
  statusCode: number;
  endpoint: string;

  constructor(statusCode: number, message: string, endpoint: string) {
    super(message);
    this.name = 'YahooApiError';
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
