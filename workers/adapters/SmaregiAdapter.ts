/**
 * Noema Retail: SmaregiAdapter
 * 
 * スマレジ（実店舗POS）との連携アダプター。
 * スマレジプラットフォームAPI を使用。
 * 
 * 圏論的解釈：
 * SmaregiAdapter は Smaregi 圏から Noema 圏への関手。
 * スマレジ固有のデータ形式を Noema の統一形式に変換。
 */

import type {
  Channel,
  InventoryEvent,
  SyncResult
} from '../attractors/InventoryAttractor';

// ============================================================================
// 型定義
// ============================================================================

export interface SmaregiConfig {
  contractId: string;
  clientId: string;
  clientSecret: string;
  accessToken: string;
  refreshToken: string;
  storeId: string;
  apiBaseUrl: string;
}

export interface SmaregiProduct {
  productId: string;
  productCode: string;
  productName: string;
  price: number;
  stockQuantity: number;
}

export interface SmaregiStock {
  productId: string;
  storeId: string;
  stockQuantity: number;
  stockAmount: number;
}

export interface SmaregiTransaction {
  transactionHeadId: string;
  transactionDateTime: string;
  storeId: string;
  terminalId: string;
  total: number;
  details: SmaregiTransactionDetail[];
}

export interface SmaregiTransactionDetail {
  productId: string;
  productCode: string;
  productName: string;
  quantity: number;
  price: number;
  subtotal: number;
}

// ============================================================================
// SmaregiAdapter
// ============================================================================

export class SmaregiAdapter {
  private config: SmaregiConfig;
  private channel: Channel = 'smaregi';

  constructor(config: SmaregiConfig) {
    this.config = config;
  }

  /**
   * API リクエストの共通処理
   */
  private async apiRequest<T>(
    method: string,
    path: string,
    body?: unknown
  ): Promise<T> {
    const url = `${this.config.apiBaseUrl}/${this.config.contractId}${path}`;
    
    const headers: Record<string, string> = {
      'Authorization': `Bearer ${this.config.accessToken}`,
      'Content-Type': 'application/json',
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
      throw new SmaregiApiError(
        response.status,
        `Smaregi API error: ${response.status} ${errorText}`
      );
    }

    return response.json() as Promise<T>;
  }

  // ==========================================================================
  // 商品操作
  // ==========================================================================

  /**
   * 商品一覧取得
   */
  async getProducts(params?: {
    limit?: number;
    page?: number;
  }): Promise<SmaregiProduct[]> {
    const query = new URLSearchParams();
    if (params?.limit) query.set('limit', String(params.limit));
    if (params?.page) query.set('page', String(params.page));

    const response = await this.apiRequest<{ products: SmaregiProduct[] }>(
      'GET',
      `/pos/products?${query.toString()}`
    );
    return response.products;
  }

  /**
   * 商品取得（単一）
   */
  async getProduct(productId: string): Promise<SmaregiProduct | null> {
    try {
      return await this.apiRequest<SmaregiProduct>(
        'GET',
        `/pos/products/${productId}`
      );
    } catch (error) {
      if (error instanceof SmaregiApiError && error.statusCode === 404) {
        return null;
      }
      throw error;
    }
  }

  // ==========================================================================
  // 在庫操作
  // ==========================================================================

  /**
   * 在庫取得
   */
  async getStock(productId: string, storeId?: string): Promise<SmaregiStock | null> {
    const targetStoreId = storeId || this.config.storeId;
    
    try {
      const response = await this.apiRequest<{ stocks: SmaregiStock[] }>(
        'GET',
        `/pos/stocks?product_id=${productId}&store_id=${targetStoreId}`
      );
      return response.stocks[0] || null;
    } catch (error) {
      if (error instanceof SmaregiApiError && error.statusCode === 404) {
        return null;
      }
      throw error;
    }
  }

  /**
   * 在庫一覧取得
   */
  async getStocks(params?: {
    storeId?: string;
    limit?: number;
    page?: number;
  }): Promise<SmaregiStock[]> {
    const query = new URLSearchParams();
    query.set('store_id', params?.storeId || this.config.storeId);
    if (params?.limit) query.set('limit', String(params.limit));
    if (params?.page) query.set('page', String(params.page));

    const response = await this.apiRequest<{ stocks: SmaregiStock[] }>(
      'GET',
      `/pos/stocks?${query.toString()}`
    );
    return response.stocks;
  }

  /**
   * 在庫更新（出荷登録による在庫減）
   * 
   * スマレジでは直接在庫を更新するのではなく、
   * 出荷登録を行うことで在庫を減らす。
   */
  async adjustStock(
    productId: string,
    delta: number,
    reason: string
  ): Promise<void> {
    if (delta < 0) {
      // 在庫減少 → 出荷登録
      await this.registerShipment(productId, Math.abs(delta), reason);
    } else if (delta > 0) {
      // 在庫増加 → 入荷登録
      await this.registerReceipt(productId, delta, reason);
    }
  }

  /**
   * 出荷登録
   */
  private async registerShipment(
    productId: string,
    quantity: number,
    reason: string
  ): Promise<void> {
    await this.apiRequest(
      'POST',
      '/pos/stock/shipment',
      {
        storeId: this.config.storeId,
        shipmentDivision: '2', // 出荷区分: 店間移動以外
        details: [{
          productId,
          quantity,
        }],
        memo: reason,
      }
    );
  }

  /**
   * 入荷登録
   */
  private async registerReceipt(
    productId: string,
    quantity: number,
    reason: string
  ): Promise<void> {
    await this.apiRequest(
      'POST',
      '/pos/stock/receipt',
      {
        storeId: this.config.storeId,
        receiptDivision: '2', // 入荷区分: 仕入以外
        details: [{
          productId,
          quantity,
        }],
        memo: reason,
      }
    );
  }

  // ==========================================================================
  // 取引操作
  // ==========================================================================

  /**
   * 取引一覧取得
   */
  async getTransactions(params: {
    from: Date;
    to: Date;
    storeId?: string;
    limit?: number;
    page?: number;
  }): Promise<SmaregiTransaction[]> {
    const query = new URLSearchParams();
    query.set('store_id', params.storeId || this.config.storeId);
    query.set('transaction_date_time_from', params.from.toISOString());
    query.set('transaction_date_time_to', params.to.toISOString());
    if (params.limit) query.set('limit', String(params.limit));
    if (params.page) query.set('page', String(params.page));

    const response = await this.apiRequest<{ transactions: SmaregiTransaction[] }>(
      'GET',
      `/pos/transactions?${query.toString()}`
    );
    return response.transactions;
  }

  /**
   * 取引を Noema の InventoryEvent に変換
   */
  transactionToInventoryEvents(transaction: SmaregiTransaction): InventoryEvent[] {
    const timestamp = new Date(transaction.transactionDateTime).getTime();
    
    return transaction.details.map(detail => ({
      eventType: 'sale' as const,
      productId: detail.productId,
      locationId: `smaregi_store_${transaction.storeId}`,
      channel: this.channel,
      delta: -detail.quantity, // 販売は在庫減少
      referenceId: transaction.transactionHeadId,
      timestamp,
      metadata: {
        productCode: detail.productCode,
        productName: detail.productName,
        price: detail.price,
        subtotal: detail.subtotal,
      },
    }));
  }

  // ==========================================================================
  // Noema 連携
  // ==========================================================================

  /**
   * スマレジの在庫を Noema に同期
   */
  async syncToNoema(
    productId: string,
    inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<SyncResult> {
    const timestamp = Date.now();
    
    try {
      // スマレジから在庫取得
      const smaregiStock = await this.getStock(productId);
      
      if (!smaregiStock) {
        return {
          success: false,
          channel: this.channel,
          error: `Product not found in Smaregi: ${productId}`,
          timestamp,
        };
      }

      // Noema に同期結果を記録
      const response = await inventoryAttractor.fetch(
        new Request('http://internal/sync', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            productId,
            channel: this.channel,
            remoteQuantity: smaregiStock.stockQuantity,
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
        quantitySynced: smaregiStock.stockQuantity,
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
   * Noema の在庫をスマレジに同期
   */
  async syncFromNoema(
    productId: string,
    noemaQuantity: number
  ): Promise<SyncResult> {
    const timestamp = Date.now();
    
    try {
      // スマレジの現在在庫を取得
      const smaregiStock = await this.getStock(productId);
      const currentQuantity = smaregiStock?.stockQuantity ?? 0;
      
      // 差分を計算
      const delta = noemaQuantity - currentQuantity;
      
      if (delta !== 0) {
        // 在庫調整
        await this.adjustStock(
          productId,
          delta,
          `Noema sync: ${currentQuantity} -> ${noemaQuantity}`
        );
      }

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
   * 新しい取引を Noema に反映
   * 
   * ポーリングまたは Webhook で呼び出される。
   */
  async processNewTransactions(
    since: Date,
    inventoryAttractor: { fetch: (request: Request) => Promise<Response> }
  ): Promise<{ processed: number; errors: string[] }> {
    const errors: string[] = [];
    let processed = 0;

    try {
      const transactions = await this.getTransactions({
        from: since,
        to: new Date(),
      });

      for (const transaction of transactions) {
        const events = this.transactionToInventoryEvents(transaction);
        
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
              `Error processing transaction ${transaction.transactionHeadId}: ${
                error instanceof Error ? error.message : 'Unknown error'
              }`
            );
          }
        }
      }
    } catch (error) {
      errors.push(
        `Failed to fetch transactions: ${
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

export class SmaregiApiError extends Error {
  statusCode: number;

  constructor(statusCode: number, message: string) {
    super(message);
    this.name = 'SmaregiApiError';
    this.statusCode = statusCode;
  }
}
