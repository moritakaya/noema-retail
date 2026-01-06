/**
 * Noema Retail: RakutenAdapter
 *
 * 楽天市場（RMS）との連携アダプター。
 * 楽天RMS WEB API（在庫API 2.0、楽天ペイ受注API）を使用。
 *
 * 圏論的解釈：
 * RakutenAdapter は Rakuten 圏から Noema 圏への関手。
 * 楽天固有のデータ形式を Noema の統一形式に変換。
 */

import type {
  Channel,
  InventoryEvent,
  SyncResult
} from '../attractors/InventoryAttractor';

// ============================================================================
// 型定義
// ============================================================================

export interface RakutenConfig {
  shopUrl: string;              // 店舗URL（例: "myshop"）
  serviceSecret: string;        // RMS WEB API serviceSecret
  licenseKey: string;           // ライセンスキー
  licenseExpiry: number;        // ライセンスキー有効期限（UNIX timestamp）
}

/** 在庫API 2.0 のレスポンス */
export interface RakutenInventory {
  manageNumber: string;         // 商品管理番号
  variantId: string;            // SKU管理番号
  quantity: number;             // 在庫数
  inventoryType?: number;       // 在庫タイプ
  restTypeFlag?: number;        // 在庫残少表示フラグ
}

export interface RakutenInventoriesResponse {
  inventories: RakutenInventory[];
}

/** 在庫更新リクエスト */
export interface RakutenInventoryUpsertItem {
  manageNumber: string;
  variantId: string;
  mode: 'ABSOLUTE' | 'RELATIVE';
  quantity: number;
}

export interface RakutenInventoryUpsertRequest {
  inventories: RakutenInventoryUpsertItem[];
}

/** 楽天ペイ受注API の注文検索リクエスト */
export interface RakutenOrderSearchRequest {
  dateType: number;
  startDatetime: string;
  endDatetime: string;
  PaginationRequestModel: {
    requestRecordsAmount: number;
    requestPage: number;
  };
}

export interface RakutenOrderSearchResponse {
  orderNumberList: string[];
  PaginationResponseModel: {
    totalRecordsAmount: number;
    totalPages: number;
    requestPage: number;
  };
}

/** 楽天ペイ受注API の注文詳細 */
export interface RakutenOrder {
  orderNumber: string;
  orderDatetime: string;
  orderStatus: string;
  orderProgress: number;
  PackageModelList: RakutenOrderPackage[];
}

export interface RakutenOrderPackage {
  basketId: number;
  ItemModelList: RakutenOrderItem[];
}

export interface RakutenOrderItem {
  itemNumber: string;
  manageNumber: string;
  itemName: string;
  units: number;
  price: number;
  selectedChoice?: string;
}

export interface RakutenOrderGetResponse {
  OrderModelList: RakutenOrder[];
}

// ============================================================================
// RakutenAdapter
// ============================================================================

export class RakutenAdapter {
  private config: RakutenConfig;
  private channel: Channel = 'rakuten';

  private static readonly API_BASE_URL = 'https://api.rms.rakuten.co.jp';

  constructor(config: RakutenConfig) {
    this.config = config;
  }

  // ==========================================================================
  // 認証・API基盤
  // ==========================================================================

  /**
   * ESA認証ヘッダーの生成
   * serviceSecret:licenseKey を Base64 エンコード
   */
  private getAuthorizationHeader(): string {
    const credentials = `${this.config.serviceSecret}:${this.config.licenseKey}`;
    const encoded = btoa(credentials);
    return `ESA ${encoded}`;
  }

  /**
   * API リクエストの共通処理
   */
  private async apiRequest<T>(
    method: 'GET' | 'POST',
    endpoint: string,
    body?: unknown
  ): Promise<T> {
    const url = `${RakutenAdapter.API_BASE_URL}${endpoint}`;

    const headers: Record<string, string> = {
      'Authorization': this.getAuthorizationHeader(),
      'Content-Type': 'application/json; charset=utf-8',
    };

    const requestInit: RequestInit = {
      method,
      headers,
    };
    if (body) {
      requestInit.body = JSON.stringify(body);
    }

    const response = await fetch(url, requestInit);

    if (!response.ok) {
      const errorText = await response.text();
      throw new RakutenApiError(
        response.status,
        `Rakuten API error: ${response.status} ${errorText}`,
        endpoint
      );
    }

    return response.json() as Promise<T>;
  }

  /**
   * ライセンスキー有効期限チェック
   */
  isLicenseExpired(): boolean {
    return Date.now() >= this.config.licenseExpiry;
  }

  /**
   * ライセンスキー有効期限の警告メッセージ取得
   */
  getLicenseExpiryWarning(): string | null {
    const daysUntilExpiry = Math.floor(
      (this.config.licenseExpiry - Date.now()) / (1000 * 60 * 60 * 24)
    );
    if (daysUntilExpiry <= 0) {
      return 'License key has expired. Please renew immediately.';
    }
    if (daysUntilExpiry <= 14) {
      return `License key expires in ${daysUntilExpiry} days.`;
    }
    return null;
  }

  // ==========================================================================
  // 在庫操作（在庫API 2.0）
  // ==========================================================================

  /**
   * 在庫取得（単一SKU）
   *
   * productId は "manageNumber:variantId" 形式を想定
   */
  async getStock(productId: string): Promise<RakutenInventory | null> {
    const [manageNumber, variantId] = this.parseProductId(productId);

    try {
      const response = await this.apiRequest<RakutenInventory>(
        'GET',
        `/es/2.0/inventories/manage-numbers/${encodeURIComponent(manageNumber)}/variants/${encodeURIComponent(variantId)}`
      );
      return response;
    } catch (error) {
      if (error instanceof RakutenApiError && error.statusCode === 404) {
        return null;
      }
      throw error;
    }
  }

  /**
   * 在庫一括取得
   */
  async getStocks(params: {
    manageNumbers?: string[];
    variantIds?: string[];
  }): Promise<RakutenInventory[]> {
    const response = await this.apiRequest<RakutenInventoriesResponse>(
      'POST',
      '/es/2.0/inventories/bulk-get',
      {
        manageNumbers: params.manageNumbers,
        variantIds: params.variantIds,
      }
    );
    return response.inventories;
  }

  /**
   * 在庫更新（一括）
   */
  async updateStocks(
    items: Array<{
      manageNumber: string;
      variantId: string;
      quantity: number;
    }>
  ): Promise<void> {
    const request: RakutenInventoryUpsertRequest = {
      inventories: items.map(item => ({
        manageNumber: item.manageNumber,
        variantId: item.variantId,
        mode: 'ABSOLUTE',
        quantity: item.quantity,
      })),
    };

    await this.apiRequest<void>(
      'POST',
      '/es/2.0/inventories/bulk-upsert',
      request
    );
  }

  /**
   * 在庫調整
   *
   * SmaregiAdapter と同じインターフェース。
   * 楽天では在庫の直接更新が可能。
   */
  async adjustStock(
    productId: string,
    delta: number,
    _reason: string
  ): Promise<void> {
    const [manageNumber, variantId] = this.parseProductId(productId);

    const current = await this.getStock(productId);
    if (!current) {
      throw new RakutenApiError(404, `Product not found: ${productId}`, 'adjustStock');
    }

    const newQuantity = current.quantity + delta;
    if (newQuantity < 0) {
      throw new Error(`Insufficient stock: current=${current.quantity}, delta=${delta}`);
    }

    await this.updateStocks([{
      manageNumber,
      variantId,
      quantity: newQuantity,
    }]);
  }

  // ==========================================================================
  // 注文操作（楽天ペイ受注API）
  // ==========================================================================

  /**
   * 注文検索
   */
  async searchOrders(params: {
    from: Date;
    to: Date;
    page?: number;
  }): Promise<string[]> {
    const request: RakutenOrderSearchRequest = {
      dateType: 1, // 注文日で検索
      startDatetime: this.formatDatetime(params.from),
      endDatetime: this.formatDatetime(params.to),
      PaginationRequestModel: {
        requestRecordsAmount: 1000,
        requestPage: params.page || 1,
      },
    };

    const response = await this.apiRequest<RakutenOrderSearchResponse>(
      'POST',
      '/es/2.0/order/searchOrder',
      request
    );

    return response.orderNumberList || [];
  }

  /**
   * 注文詳細取得
   */
  async getOrders(orderNumbers: string[]): Promise<RakutenOrder[]> {
    if (orderNumbers.length === 0) return [];

    // 100件ずつ分割して取得
    const chunks: string[][] = [];
    for (let i = 0; i < orderNumbers.length; i += 100) {
      chunks.push(orderNumbers.slice(i, i + 100));
    }

    const allOrders: RakutenOrder[] = [];

    for (const chunk of chunks) {
      const response = await this.apiRequest<RakutenOrderGetResponse>(
        'POST',
        '/es/2.0/order/getOrder',
        { orderNumberList: chunk }
      );
      allOrders.push(...(response.OrderModelList || []));
    }

    return allOrders;
  }

  /**
   * 注文を Noema の InventoryEvent に変換
   */
  orderToInventoryEvents(order: RakutenOrder): InventoryEvent[] {
    const timestamp = new Date(order.orderDatetime).getTime();
    const events: InventoryEvent[] = [];

    for (const pkg of order.PackageModelList || []) {
      for (const item of pkg.ItemModelList || []) {
        const variantId = item.selectedChoice || 'default';
        events.push({
          eventType: 'sale' as const,
          productId: `${item.manageNumber}:${variantId}`,
          locationId: `rakuten_${this.config.shopUrl}`,
          channel: this.channel,
          delta: -item.units,
          referenceId: order.orderNumber,
          timestamp,
          metadata: {
            itemNumber: item.itemNumber,
            itemName: item.itemName,
            price: item.price,
            basketId: pkg.basketId,
          },
        });
      }
    }

    return events;
  }

  // ==========================================================================
  // Noema 連携
  // ==========================================================================

  /**
   * 楽天の在庫を Noema に同期
   */
  async syncToNoema(
    productId: string,
    inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<SyncResult> {
    const timestamp = Date.now();

    try {
      if (this.isLicenseExpired()) {
        return {
          success: false,
          channel: this.channel,
          error: 'Rakuten license key has expired',
          timestamp,
        };
      }

      const rakutenStock = await this.getStock(productId);

      if (!rakutenStock) {
        return {
          success: false,
          channel: this.channel,
          error: `Product not found in Rakuten: ${productId}`,
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
            remoteQuantity: rakutenStock.quantity,
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
        quantitySynced: rakutenStock.quantity,
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
   * Noema の在庫を楽天に同期
   */
  async syncFromNoema(
    productId: string,
    noemaQuantity: number
  ): Promise<SyncResult> {
    const timestamp = Date.now();

    try {
      if (this.isLicenseExpired()) {
        return {
          success: false,
          channel: this.channel,
          error: 'Rakuten license key has expired',
          timestamp,
        };
      }

      const [manageNumber, variantId] = this.parseProductId(productId);

      await this.updateStocks([{
        manageNumber,
        variantId,
        quantity: noemaQuantity,
      }]);

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
      const orderNumbers = await this.searchOrders({
        from: since,
        to: new Date(),
      });

      if (orderNumbers.length === 0) {
        return { processed: 0, errors: [] };
      }

      const orders = await this.getOrders(orderNumbers);

      for (const order of orders) {
        const events = this.orderToInventoryEvents(order);

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
              errors.push(`Failed to process event: ${errorText}`);
            }
          } catch (error) {
            errors.push(
              `Error processing order ${order.orderNumber}: ${
                error instanceof Error ? error.message : 'Unknown error'
              }`
            );
          }
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
   * productId を manageNumber と variantId に分解
   * 形式: "manageNumber:variantId"
   */
  private parseProductId(productId: string): [string, string] {
    const parts = productId.split(':');
    if (parts.length < 2) {
      return [productId, 'default'];
    }
    return [parts[0], parts.slice(1).join(':')];
  }

  /**
   * 楽天API用の日時フォーマット（ISO 8601）
   */
  private formatDatetime(date: Date): string {
    return date.toISOString().replace('Z', '+09:00');
  }
}

// ============================================================================
// エラークラス
// ============================================================================

export class RakutenApiError extends Error {
  statusCode: number;
  endpoint: string;

  constructor(statusCode: number, message: string, endpoint: string) {
    super(message);
    this.name = 'RakutenApiError';
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
