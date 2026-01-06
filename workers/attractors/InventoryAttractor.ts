/**
 * Noema Retail: InventoryAttractor
 * 
 * 在庫管理を担当する Durable Object。
 * 
 * 圏論的解釈：
 * - InventoryAttractor は A-algebra として機能
 * - Intent（InventoryF）を受け取り、状態を更新
 * - SQLite に状態を永続化（沈殿）
 * 
 * 設計原則：
 * - Single Source of Truth: この DO が在庫の真実
 * - イベントソーシング: 全変動をログに記録
 * - 楽観的ロック: 同時更新の検出と解決
 */

import { DurableObject } from "cloudflare:workers";

// ============================================================================
// 型定義
// ============================================================================

export interface Inventory {
  id: string;
  productId: string;
  locationId: string;
  quantity: number;
  reserved: number;
  updatedAt: number;
}

export interface InventoryEvent {
  eventType: InventoryEventType;
  productId: string;
  locationId: string;
  channel: Channel;
  delta: number;
  referenceId?: string;
  timestamp: number;
  metadata?: Record<string, unknown>;
}

export type InventoryEventType = 
  | 'sale' 
  | 'purchase' 
  | 'adjust' 
  | 'transfer' 
  | 'reserve' 
  | 'release' 
  | 'return';

export type Channel = 
  | 'rakuten' 
  | 'yahoo' 
  | 'smaregi' 
  | 'self_ec' 
  | string;

export interface ChannelSyncStatus {
  productId: string;
  channel: Channel;
  localQuantity: number;
  remoteQuantity: number | null;
  syncStatus: SyncStatus;
  lastSyncAt: number | null;
  lastError: string | null;
}

export type SyncStatus = 'synced' | 'pending' | 'error' | 'conflict';

export interface SyncResult {
  success: boolean;
  channel: Channel;
  quantitySynced?: number;
  error?: string;
  timestamp: number;
}

export interface Reservation {
  id: string;
  inventoryId: string;
  quantity: number;
  orderId?: string;
  channel: Channel;
  expiresAt: number;
  createdAt: number;
}

// ============================================================================
// InventoryAttractor
// ============================================================================

export class InventoryAttractor extends DurableObject {
  private sql: SqlStorage;
  private initialized = false;

  constructor(ctx: DurableObjectState, env: Env) {
    super(ctx, env);
    this.sql = ctx.storage.sql;
  }

  /**
   * 初期化（スキーマ作成）
   */
  private async ensureInitialized(): Promise<void> {
    if (this.initialized) return;

    // 在庫テーブル
    this.sql.exec(`
      CREATE TABLE IF NOT EXISTS inventory (
        id TEXT PRIMARY KEY,
        product_id TEXT NOT NULL,
        location_id TEXT NOT NULL,
        quantity INTEGER NOT NULL DEFAULT 0,
        reserved INTEGER NOT NULL DEFAULT 0,
        updated_at INTEGER NOT NULL,
        UNIQUE(product_id, location_id)
      )
    `);

    // 在庫ログテーブル（イベントソーシング）
    this.sql.exec(`
      CREATE TABLE IF NOT EXISTS inventory_log (
        id TEXT PRIMARY KEY,
        inventory_id TEXT NOT NULL,
        event_type TEXT NOT NULL,
        channel TEXT NOT NULL,
        delta INTEGER NOT NULL,
        reference_id TEXT,
        quantity_before INTEGER NOT NULL,
        quantity_after INTEGER NOT NULL,
        created_at INTEGER NOT NULL,
        metadata TEXT
      )
    `);

    // チャネル同期状態テーブル
    this.sql.exec(`
      CREATE TABLE IF NOT EXISTS channel_sync (
        product_id TEXT NOT NULL,
        channel TEXT NOT NULL,
        local_quantity INTEGER NOT NULL,
        remote_quantity INTEGER,
        sync_status TEXT NOT NULL DEFAULT 'pending',
        last_sync_at INTEGER,
        last_error TEXT,
        PRIMARY KEY (product_id, channel)
      )
    `);

    // 予約テーブル
    this.sql.exec(`
      CREATE TABLE IF NOT EXISTS reservation (
        id TEXT PRIMARY KEY,
        inventory_id TEXT NOT NULL,
        quantity INTEGER NOT NULL,
        order_id TEXT,
        channel TEXT NOT NULL,
        expires_at INTEGER NOT NULL,
        created_at INTEGER NOT NULL
      )
    `);

    // インデックス
    this.sql.exec(`
      CREATE INDEX IF NOT EXISTS idx_inventory_product ON inventory(product_id);
      CREATE INDEX IF NOT EXISTS idx_log_inventory ON inventory_log(inventory_id);
      CREATE INDEX IF NOT EXISTS idx_log_created ON inventory_log(created_at);
      CREATE INDEX IF NOT EXISTS idx_reservation_expires ON reservation(expires_at);
    `);

    this.initialized = true;
  }

  // ==========================================================================
  // HTTP ハンドラー
  // ==========================================================================

  async fetch(request: Request): Promise<Response> {
    await this.ensureInitialized();

    const url = new URL(request.url);
    const path = url.pathname;

    try {
      // GET /inventory/:productId/:locationId
      if (request.method === 'GET' && path.startsWith('/inventory/')) {
        const parts = path.split('/').filter(p => p);
        if (parts.length === 3) {
          const [, productId, locationId] = parts;
          const inventory = this.getInventory(productId, locationId);
          return Response.json(inventory);
        }
        if (parts.length === 2) {
          const [, productId] = parts;
          const inventories = this.getInventoryByProduct(productId);
          return Response.json(inventories);
        }
      }

      // POST /inventory - 在庫作成/更新
      if (request.method === 'POST' && path === '/inventory') {
        const body = await request.json() as {
          productId: string;
          locationId: string;
          quantity: number;
        };
        const inventory = this.createOrUpdateInventory(
          body.productId,
          body.locationId,
          body.quantity
        );
        return Response.json(inventory);
      }

      // POST /adjust - 在庫調整
      if (request.method === 'POST' && path === '/adjust') {
        const body = await request.json() as {
          productId: string;
          locationId: string;
          delta: number;
          eventType: InventoryEventType;
          channel: Channel;
          referenceId?: string;
          metadata?: Record<string, unknown>;
        };
        const result = this.adjustStock(body);
        return Response.json(result);
      }

      // POST /reserve - 在庫予約
      if (request.method === 'POST' && path === '/reserve') {
        const body = await request.json() as {
          productId: string;
          locationId: string;
          quantity: number;
          channel: Channel;
          orderId?: string;
          expiresInMs?: number;
        };
        const reservation = this.reserveStock(body);
        if (reservation) {
          return Response.json(reservation);
        }
        return Response.json({ error: 'Insufficient stock' }, { status: 400 });
      }

      // DELETE /reserve/:reservationId - 予約解除
      if (request.method === 'DELETE' && path.startsWith('/reserve/')) {
        const reservationId = path.split('/')[2];
        const success = this.releaseReservation(reservationId);
        return Response.json({ success });
      }

      // POST /sync - チャネル同期
      if (request.method === 'POST' && path === '/sync') {
        const body = await request.json() as {
          productId: string;
          channel: Channel;
          remoteQuantity: number;
        };
        const result = this.recordSync(body);
        return Response.json(result);
      }

      // GET /sync/:productId - 同期状態取得
      if (request.method === 'GET' && path.startsWith('/sync/')) {
        const productId = path.split('/')[2];
        const statuses = this.getSyncStatuses(productId);
        return Response.json(statuses);
      }

      // GET /log/:productId - ログ取得
      if (request.method === 'GET' && path.startsWith('/log/')) {
        const productId = path.split('/')[2];
        const from = parseInt(url.searchParams.get('from') || '0');
        const to = parseInt(url.searchParams.get('to') || String(Date.now()));
        const logs = this.getInventoryLog(productId, from, to);
        return Response.json(logs);
      }

      return Response.json({ error: 'Not found' }, { status: 404 });
    } catch (error) {
      console.error('InventoryAttractor error:', error);
      return Response.json(
        { error: error instanceof Error ? error.message : 'Unknown error' },
        { status: 500 }
      );
    }
  }

  // ==========================================================================
  // 在庫操作
  // ==========================================================================

  /**
   * 在庫取得
   */
  getInventory(productId: string, locationId: string): Inventory | null {
    const result = this.sql.exec<Inventory>(
      `SELECT id, product_id as productId, location_id as locationId, 
              quantity, reserved, updated_at as updatedAt
       FROM inventory 
       WHERE product_id = ? AND location_id = ?`,
      productId, locationId
    );
    return result.one() || null;
  }

  /**
   * 商品の全在庫取得
   */
  getInventoryByProduct(productId: string): Inventory[] {
    const result = this.sql.exec<Inventory>(
      `SELECT id, product_id as productId, location_id as locationId,
              quantity, reserved, updated_at as updatedAt
       FROM inventory 
       WHERE product_id = ?`,
      productId
    );
    return result.toArray();
  }

  /**
   * 在庫作成/更新
   */
  createOrUpdateInventory(
    productId: string, 
    locationId: string, 
    quantity: number
  ): Inventory {
    const now = Date.now();
    const id = `inv_${productId}_${locationId}`;

    this.sql.exec(
      `INSERT INTO inventory (id, product_id, location_id, quantity, reserved, updated_at)
       VALUES (?, ?, ?, ?, 0, ?)
       ON CONFLICT(product_id, location_id) DO UPDATE SET
         quantity = excluded.quantity,
         updated_at = excluded.updated_at`,
      id, productId, locationId, quantity, now
    );

    return this.getInventory(productId, locationId)!;
  }

  /**
   * 在庫調整
   * 
   * Intent（InventoryF.AdjustStock）の実行。
   * イベントをログに記録し、在庫を更新。
   */
  adjustStock(params: {
    productId: string;
    locationId: string;
    delta: number;
    eventType: InventoryEventType;
    channel: Channel;
    referenceId?: string;
    metadata?: Record<string, unknown>;
  }): { inventory: Inventory; logId: string } {
    const now = Date.now();
    const inventory = this.getInventory(params.productId, params.locationId);

    if (!inventory) {
      throw new Error(`Inventory not found: ${params.productId}/${params.locationId}`);
    }

    const quantityBefore = inventory.quantity;
    const quantityAfter = quantityBefore + params.delta;

    if (quantityAfter < 0) {
      throw new Error(`Insufficient stock: current=${quantityBefore}, delta=${params.delta}`);
    }

    // 在庫更新
    this.sql.exec(
      `UPDATE inventory SET quantity = ?, updated_at = ? WHERE id = ?`,
      quantityAfter, now, inventory.id
    );

    // ログ記録
    const logId = `log_${crypto.randomUUID()}`;
    this.sql.exec(
      `INSERT INTO inventory_log 
       (id, inventory_id, event_type, channel, delta, reference_id, 
        quantity_before, quantity_after, created_at, metadata)
       VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
      logId, inventory.id, params.eventType, params.channel, params.delta,
      params.referenceId || null, quantityBefore, quantityAfter, now,
      params.metadata ? JSON.stringify(params.metadata) : null
    );

    // チャネル同期状態を pending に
    this.sql.exec(
      `INSERT INTO channel_sync (product_id, channel, local_quantity, sync_status)
       VALUES (?, ?, ?, 'pending')
       ON CONFLICT(product_id, channel) DO UPDATE SET
         local_quantity = excluded.local_quantity,
         sync_status = 'pending'`,
      params.productId, params.channel, quantityAfter
    );

    return {
      inventory: this.getInventory(params.productId, params.locationId)!,
      logId
    };
  }

  /**
   * 在庫予約
   * 
   * available (quantity - reserved) から予約分を確保。
   */
  reserveStock(params: {
    productId: string;
    locationId: string;
    quantity: number;
    channel: Channel;
    orderId?: string;
    expiresInMs?: number;
  }): Reservation | null {
    const inventory = this.getInventory(params.productId, params.locationId);
    if (!inventory) return null;

    const available = inventory.quantity - inventory.reserved;
    if (available < params.quantity) return null;

    const now = Date.now();
    const expiresAt = now + (params.expiresInMs || 15 * 60 * 1000); // デフォルト15分
    const reservationId = `rsv_${crypto.randomUUID()}`;

    // 予約を記録
    this.sql.exec(
      `INSERT INTO reservation (id, inventory_id, quantity, order_id, channel, expires_at, created_at)
       VALUES (?, ?, ?, ?, ?, ?, ?)`,
      reservationId, inventory.id, params.quantity, params.orderId || null,
      params.channel, expiresAt, now
    );

    // reserved を更新
    this.sql.exec(
      `UPDATE inventory SET reserved = reserved + ?, updated_at = ? WHERE id = ?`,
      params.quantity, now, inventory.id
    );

    return {
      id: reservationId,
      inventoryId: inventory.id,
      quantity: params.quantity,
      orderId: params.orderId,
      channel: params.channel,
      expiresAt,
      createdAt: now
    };
  }

  /**
   * 予約解除
   */
  releaseReservation(reservationId: string): boolean {
    const result = this.sql.exec<Reservation>(
      `SELECT id, inventory_id as inventoryId, quantity, order_id as orderId,
              channel, expires_at as expiresAt, created_at as createdAt
       FROM reservation WHERE id = ?`,
      reservationId
    );
    const reservation = result.one();
    if (!reservation) return false;

    const now = Date.now();

    // reserved を減算
    this.sql.exec(
      `UPDATE inventory SET reserved = reserved - ?, updated_at = ? WHERE id = ?`,
      reservation.quantity, now, reservation.inventoryId
    );

    // 予約を削除
    this.sql.exec(`DELETE FROM reservation WHERE id = ?`, reservationId);

    return true;
  }

  // ==========================================================================
  // 同期操作
  // ==========================================================================

  /**
   * 同期結果を記録
   */
  recordSync(params: {
    productId: string;
    channel: Channel;
    remoteQuantity: number;
  }): ChannelSyncStatus {
    const now = Date.now();
    const inventory = this.getInventoryByProduct(params.productId);
    const totalQuantity = inventory.reduce((sum, inv) => sum + inv.quantity, 0);

    // コンフリクト検出
    const syncStatus: SyncStatus = 
      Math.abs(totalQuantity - params.remoteQuantity) <= 1 
        ? 'synced' 
        : 'conflict';

    this.sql.exec(
      `INSERT INTO channel_sync 
       (product_id, channel, local_quantity, remote_quantity, sync_status, last_sync_at)
       VALUES (?, ?, ?, ?, ?, ?)
       ON CONFLICT(product_id, channel) DO UPDATE SET
         local_quantity = excluded.local_quantity,
         remote_quantity = excluded.remote_quantity,
         sync_status = excluded.sync_status,
         last_sync_at = excluded.last_sync_at,
         last_error = NULL`,
      params.productId, params.channel, totalQuantity, 
      params.remoteQuantity, syncStatus, now
    );

    return this.getSyncStatus(params.productId, params.channel)!;
  }

  /**
   * 同期状態取得
   */
  getSyncStatus(productId: string, channel: Channel): ChannelSyncStatus | null {
    const result = this.sql.exec<ChannelSyncStatus>(
      `SELECT product_id as productId, channel, local_quantity as localQuantity,
              remote_quantity as remoteQuantity, sync_status as syncStatus,
              last_sync_at as lastSyncAt, last_error as lastError
       FROM channel_sync
       WHERE product_id = ? AND channel = ?`,
      productId, channel
    );
    return result.one() || null;
  }

  /**
   * 商品の全同期状態取得
   */
  getSyncStatuses(productId: string): ChannelSyncStatus[] {
    const result = this.sql.exec<ChannelSyncStatus>(
      `SELECT product_id as productId, channel, local_quantity as localQuantity,
              remote_quantity as remoteQuantity, sync_status as syncStatus,
              last_sync_at as lastSyncAt, last_error as lastError
       FROM channel_sync
       WHERE product_id = ?`,
      productId
    );
    return result.toArray();
  }

  // ==========================================================================
  // ログ操作
  // ==========================================================================

  /**
   * 在庫ログ取得
   */
  getInventoryLog(productId: string, from: number, to: number): InventoryLogEntry[] {
    const result = this.sql.exec<InventoryLogEntry>(
      `SELECT l.id, l.inventory_id as inventoryId, l.event_type as eventType,
              l.channel, l.delta, l.reference_id as referenceId,
              l.quantity_before as quantityBefore, l.quantity_after as quantityAfter,
              l.created_at as createdAt, l.metadata
       FROM inventory_log l
       JOIN inventory i ON l.inventory_id = i.id
       WHERE i.product_id = ? AND l.created_at BETWEEN ? AND ?
       ORDER BY l.created_at DESC`,
      productId, from, to
    );
    return result.toArray();
  }

  // ==========================================================================
  // Alarm（期限切れ予約の処理）
  // ==========================================================================

  async alarm(): Promise<void> {
    await this.ensureInitialized();
    const now = Date.now();

    // 期限切れの予約を取得
    const expired = this.sql.exec<Reservation>(
      `SELECT id, inventory_id as inventoryId, quantity, order_id as orderId,
              channel, expires_at as expiresAt, created_at as createdAt
       FROM reservation WHERE expires_at <= ?`,
      now
    );

    // 期限切れ予約を解除
    for (const reservation of expired.toArray()) {
      this.releaseReservation(reservation.id);
      console.log(`Released expired reservation: ${reservation.id}`);
    }

    // 次の Alarm をセット（1分後）
    await this.ctx.storage.setAlarm(now + 60000);
  }
}

// 型定義
interface InventoryLogEntry {
  id: string;
  inventoryId: string;
  eventType: InventoryEventType;
  channel: Channel;
  delta: number;
  referenceId: string | null;
  quantityBefore: number;
  quantityAfter: number;
  createdAt: number;
  metadata: string | null;
}

interface Env {
  // 環境変数
}
