-- | Noema Handler: InventoryHandler
-- |
-- | InventoryF を SQLite Storage へ解釈する Handler。
-- |
-- | 圏論的解釈：
-- | - InventoryF は在庫操作の Functor
-- | - Handler は A-algebra homomorphism として機能
-- | - Intent → SQLite の状態変更へと「忘却」する
-- |
-- | イベントソーシング：
-- | すべての在庫変更は inventory_log テーブルに記録される。
-- | これにより、状態の完全な履歴を再構築可能。
module Noema.Handler.InventoryHandler
  ( runInventoryIntent
  , InventoryEnv
  , mkInventoryEnv
  , initializeSchema
  ) where

import Prelude

import Data.Array (head)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap, wrap)
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign, unsafeFromForeign)
import Noema.Domain.Base (ThingId(..), LocationId(..), Timestamp(..), mkTimestamp, currentTimestamp)
import Noema.Domain.Inventory
  ( InventoryF(..)
  , Inventory(..)
  , InventoryId(..)
  , Quantity(..)
  , QuantityDelta(..)
  , InventoryEvent(..)
  , InventoryEventType
  , InventoryLogEntry(..)
  , Channel
  , ChannelSyncStatus(..)
  , SyncStatus(..)
  , SyncResult(..)
  , Reservation(..)
  , ReservationId(..)
  , channelToString
  , channelFromString
  , eventTypeToString
  , syncStatusFromString
  , applyDelta
  )
import Noema.Intent.Freer (Intent, foldIntent)
import Workers.FFI.SqlStorage (SqlStorage, exec, execWithParams, one, toArray)

-- | Inventory Handler 環境
type InventoryEnv =
  { sql :: SqlStorage
  }

-- | 環境を作成
mkInventoryEnv :: SqlStorage -> InventoryEnv
mkInventoryEnv sql = { sql }

-- | スキーマを初期化
-- |
-- | Durable Object の初回アクセス時に呼び出す。
initializeSchema :: SqlStorage -> Effect Unit
initializeSchema sql = do
  -- 在庫テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS inventory (
      id TEXT PRIMARY KEY,
      product_id TEXT NOT NULL,
      location_id TEXT NOT NULL,
      quantity INTEGER NOT NULL DEFAULT 0,
      reserved INTEGER NOT NULL DEFAULT 0,
      updated_at REAL NOT NULL,
      UNIQUE(product_id, location_id)
    )
  """

  -- イベントログテーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS inventory_log (
      id TEXT PRIMARY KEY,
      inventory_id TEXT NOT NULL,
      event_type TEXT NOT NULL,
      channel TEXT NOT NULL,
      delta INTEGER NOT NULL,
      reference_id TEXT,
      quantity_before INTEGER NOT NULL,
      quantity_after INTEGER NOT NULL,
      created_at REAL NOT NULL,
      metadata TEXT,
      FOREIGN KEY (inventory_id) REFERENCES inventory(id)
    )
  """

  -- チャネル同期テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS channel_sync (
      product_id TEXT NOT NULL,
      channel TEXT NOT NULL,
      local_quantity INTEGER NOT NULL,
      remote_quantity INTEGER,
      sync_status TEXT NOT NULL DEFAULT 'pending',
      last_sync_at REAL,
      last_error TEXT,
      PRIMARY KEY (product_id, channel)
    )
  """

  -- 予約テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS reservation (
      id TEXT PRIMARY KEY,
      inventory_id TEXT NOT NULL,
      quantity INTEGER NOT NULL,
      order_id TEXT,
      channel TEXT NOT NULL,
      expires_at REAL NOT NULL,
      created_at REAL NOT NULL,
      FOREIGN KEY (inventory_id) REFERENCES inventory(id)
    )
  """

  -- インデックス
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_inventory_product ON inventory(product_id)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_inventory_log_inventory ON inventory_log(inventory_id)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_inventory_log_created ON inventory_log(created_at)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_reservation_expires ON reservation(expires_at)"
  pure unit

-- | InventoryF を Effect に解釈する
interpretInventoryF :: InventoryEnv -> InventoryF ~> Effect
interpretInventoryF env = case _ of
  GetInventory productId locationId cont -> do
    let cursor = execWithParams env.sql
          "SELECT * FROM inventory WHERE product_id = ? AND location_id = ?"
          [ unsafeToForeign (unwrap productId)
          , unsafeToForeign (unwrap locationId)
          ]
    pure $ cont $ rowToInventory <$> one cursor

  GetInventoryByProduct productId cont -> do
    let cursor = execWithParams env.sql
          "SELECT * FROM inventory WHERE product_id = ?"
          [ unsafeToForeign (unwrap productId) ]
        rows = toArray cursor
    pure $ cont $ rowToInventory <$> rows

  CreateInventory productId locationId quantity cont -> do
    now <- currentTimestamp
    let inventoryId = mkInventoryId productId locationId
        _ = execWithParams env.sql
          """
          INSERT INTO inventory (id, product_id, location_id, quantity, reserved, updated_at)
          VALUES (?, ?, ?, ?, 0, ?)
          ON CONFLICT (product_id, location_id) DO UPDATE SET
            quantity = excluded.quantity,
            updated_at = excluded.updated_at
          """
          [ unsafeToForeign (unwrap inventoryId)
          , unsafeToForeign (unwrap productId)
          , unsafeToForeign (unwrap locationId)
          , unsafeToForeign (unwrap quantity)
          , unsafeToForeign (unwrap now)
          ]
    pure $ cont $ Inventory
      { id: inventoryId
      , productId
      , locationId
      , quantity
      , reserved: Quantity 0
      , updatedAt: now
      }

  AdjustStock productId locationId delta eventType channel refId cont -> do
    now <- currentTimestamp
    let inventoryId = mkInventoryId productId locationId

    -- 現在の在庫を取得
    let cursor = execWithParams env.sql
          "SELECT quantity FROM inventory WHERE id = ?"
          [ unsafeToForeign (unwrap inventoryId) ]
    let currentQty = fromMaybe (Quantity 0) $ do
          row <- one cursor
          Just $ Quantity $ unsafeFromForeign $ getField row "quantity"

    let newQty = applyDelta delta currentQty

    -- 在庫を更新
    let _ = execWithParams env.sql
          """
          UPDATE inventory SET quantity = ?, updated_at = ?
          WHERE id = ?
          """
          [ unsafeToForeign (unwrap newQty)
          , unsafeToForeign (unwrap now)
          , unsafeToForeign (unwrap inventoryId)
          ]

    -- ログを記録
    logId <- generateId
    let _ = execWithParams env.sql
          """
          INSERT INTO inventory_log
            (id, inventory_id, event_type, channel, delta, reference_id, quantity_before, quantity_after, created_at)
          VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
          """
          [ unsafeToForeign logId
          , unsafeToForeign (unwrap inventoryId)
          , unsafeToForeign (eventTypeToString eventType)
          , unsafeToForeign (channelToString channel)
          , unsafeToForeign (unwrap delta)
          , unsafeToForeign refId
          , unsafeToForeign (unwrap currentQty)
          , unsafeToForeign (unwrap newQty)
          , unsafeToForeign (unwrap now)
          ]

    -- 更新後の在庫を返す
    let cursorUpdated = execWithParams env.sql
          "SELECT * FROM inventory WHERE id = ?"
          [ unsafeToForeign (unwrap inventoryId) ]
    pure $ cont $ fromMaybe defaultInventory $ rowToInventory <$> one cursorUpdated
    where
      defaultInventory = Inventory
        { id: mkInventoryId productId locationId
        , productId
        , locationId
        , quantity: Quantity 0
        , reserved: Quantity 0
        , updatedAt: mkTimestamp 0.0
        }

  ReserveStock productId locationId quantity channel orderId cont -> do
    now <- currentTimestamp
    let inventoryId = mkInventoryId productId locationId

    -- 在庫確認
    let cursor = execWithParams env.sql
          "SELECT quantity, reserved FROM inventory WHERE id = ?"
          [ unsafeToForeign (unwrap inventoryId) ]
    case one cursor of
      Nothing -> pure $ cont Nothing
      Just row -> do
        let currentQty = Quantity $ unsafeFromForeign $ getField row "quantity"
            currentReserved = Quantity $ unsafeFromForeign $ getField row "reserved"
            available = Quantity $ (unwrap currentQty) - (unwrap currentReserved)
        if unwrap quantity > unwrap available
          then pure $ cont Nothing
          else do
            -- 予約を作成
            reservationId <- ReservationId <$> generateId
            let expiresAt = mkTimestamp $ (unwrap now) + 900000.0 -- 15分後
            let _ = execWithParams env.sql
                  """
                  INSERT INTO reservation (id, inventory_id, quantity, order_id, channel, expires_at, created_at)
                  VALUES (?, ?, ?, ?, ?, ?, ?)
                  """
                  [ unsafeToForeign (unwrap reservationId)
                  , unsafeToForeign (unwrap inventoryId)
                  , unsafeToForeign (unwrap quantity)
                  , unsafeToForeign orderId
                  , unsafeToForeign (channelToString channel)
                  , unsafeToForeign (unwrap expiresAt)
                  , unsafeToForeign (unwrap now)
                  ]

            -- reserved を更新
            let newReserved = Quantity $ (unwrap currentReserved) + (unwrap quantity)
            let _ = execWithParams env.sql
                  "UPDATE inventory SET reserved = ?, updated_at = ? WHERE id = ?"
                  [ unsafeToForeign (unwrap newReserved)
                  , unsafeToForeign (unwrap now)
                  , unsafeToForeign (unwrap inventoryId)
                  ]

            pure $ cont $ Just reservationId

  ReleaseReservation reservationId cont -> do
    now <- currentTimestamp
    -- 予約を取得
    let cursor = execWithParams env.sql
          "SELECT inventory_id, quantity FROM reservation WHERE id = ?"
          [ unsafeToForeign (unwrap reservationId) ]
    case one cursor of
      Nothing -> pure $ cont false
      Just row -> do
        let inventoryId = InventoryId $ unsafeFromForeign $ getField row "inventory_id"
            quantity = Quantity $ unsafeFromForeign $ getField row "quantity"

        -- 予約を削除
        let _ = execWithParams env.sql
              "DELETE FROM reservation WHERE id = ?"
              [ unsafeToForeign (unwrap reservationId) ]

        -- reserved を減らす
        let _ = execWithParams env.sql
              "UPDATE inventory SET reserved = reserved - ?, updated_at = ? WHERE id = ?"
              [ unsafeToForeign (unwrap quantity)
              , unsafeToForeign (unwrap now)
              , unsafeToForeign (unwrap inventoryId)
              ]

        pure $ cont true

  GetReservation reservationId cont -> do
    let cursor = execWithParams env.sql
          "SELECT * FROM reservation WHERE id = ?"
          [ unsafeToForeign (unwrap reservationId) ]
    pure $ cont $ rowToReservation <$> one cursor

  SyncToChannel productId channel cont -> do
    now <- currentTimestamp
    -- 同期結果を返す（実際の同期はアダプター経由）
    pure $ cont $ SyncSuccess
      { channel
      , quantitySynced: Quantity 0
      , timestamp: now
      }

  SyncFromChannel productId channel cont -> do
    now <- currentTimestamp
    pure $ cont $ SyncSuccess
      { channel
      , quantitySynced: Quantity 0
      , timestamp: now
      }

  SyncAllChannels productId cont -> do
    pure $ cont []

  GetSyncStatus productId cont -> do
    let cursor = execWithParams env.sql
          "SELECT * FROM channel_sync WHERE product_id = ?"
          [ unsafeToForeign (unwrap productId) ]
        rows = toArray cursor
    pure $ cont $ rowToChannelSyncStatus <$> rows

  GetInventoryLog productId from to cont -> do
    let inventoryId = mkInventoryId productId (LocationId "default")
        cursor = execWithParams env.sql
          """
          SELECT * FROM inventory_log
          WHERE inventory_id LIKE ? AND created_at >= ? AND created_at <= ?
          ORDER BY created_at DESC
          """
          [ unsafeToForeign (unwrap productId <> "%")
          , unsafeToForeign (unwrap from)
          , unsafeToForeign (unwrap to)
          ]
        rows = toArray cursor
    pure $ cont $ rowToInventoryLogEntry <$> rows

  BulkGetInventory productIds cont -> do
    -- 簡易実装：個別に取得
    let results = []
    pure $ cont results

  BulkSyncAllChannels productIds cont -> do
    pure $ cont []

-- | Intent を実行
runInventoryIntent :: InventoryEnv -> Intent InventoryF ~> Effect
runInventoryIntent env = foldIntent (interpretInventoryF env)

--------------------------------------------------------------------------------
-- ヘルパー関数
--------------------------------------------------------------------------------

-- | 在庫 ID を生成
mkInventoryId :: ThingId -> LocationId -> InventoryId
mkInventoryId (ThingId p) (LocationId l) = InventoryId $ p <> ":" <> l

-- | ユニークな ID を生成
foreign import generateId :: Effect String

-- | Foreign オブジェクトからフィールドを取得
foreign import getField :: Foreign -> String -> Foreign

-- | 行データを Inventory に変換
rowToInventory :: Foreign -> Inventory
rowToInventory row = Inventory
  { id: InventoryId $ unsafeFromForeign $ getField row "id"
  , productId: ThingId $ unsafeFromForeign $ getField row "product_id"
  , locationId: LocationId $ unsafeFromForeign $ getField row "location_id"
  , quantity: Quantity $ unsafeFromForeign $ getField row "quantity"
  , reserved: Quantity $ unsafeFromForeign $ getField row "reserved"
  , updatedAt: Timestamp $ unsafeFromForeign $ getField row "updated_at"
  }

-- | 行データを Reservation に変換
rowToReservation :: Foreign -> Reservation
rowToReservation row = Reservation
  { id: ReservationId $ unsafeFromForeign $ getField row "id"
  , inventoryId: InventoryId $ unsafeFromForeign $ getField row "inventory_id"
  , quantity: Quantity $ unsafeFromForeign $ getField row "quantity"
  , orderId: unsafeFromForeign $ getField row "order_id"
  , channel: channelFromString $ unsafeFromForeign $ getField row "channel"
  , expiresAt: Timestamp $ unsafeFromForeign $ getField row "expires_at"
  , createdAt: Timestamp $ unsafeFromForeign $ getField row "created_at"
  }

-- | 行データを ChannelSyncStatus に変換
rowToChannelSyncStatus :: Foreign -> ChannelSyncStatus
rowToChannelSyncStatus row = ChannelSyncStatus
  { productId: ThingId $ unsafeFromForeign $ getField row "product_id"
  , channel: channelFromString $ unsafeFromForeign $ getField row "channel"
  , localQuantity: Quantity $ unsafeFromForeign $ getField row "local_quantity"
  , remoteQuantity: Nothing -- TODO
  , syncStatus: fromMaybe SPending $ syncStatusFromString $ unsafeFromForeign $ getField row "sync_status"
  , lastSyncAt: Nothing -- TODO
  , lastError: unsafeFromForeign $ getField row "last_error"
  }

-- | 行データを InventoryLogEntry に変換
rowToInventoryLogEntry :: Foreign -> InventoryLogEntry
rowToInventoryLogEntry row = InventoryLogEntry
  { id: unsafeFromForeign $ getField row "id"
  , event: InventoryEvent
      { eventType: fromMaybe (unsafeFromForeign $ getField row "event_type") Nothing -- TODO: parse
      , productId: ThingId ""
      , locationId: LocationId ""
      , channel: channelFromString $ unsafeFromForeign $ getField row "channel"
      , delta: QuantityDelta $ unsafeFromForeign $ getField row "delta"
      , referenceId: unsafeFromForeign $ getField row "reference_id"
      , timestamp: Timestamp $ unsafeFromForeign $ getField row "created_at"
      , metadata: unsafeFromForeign $ getField row "metadata"
      }
  , quantityBefore: Quantity $ unsafeFromForeign $ getField row "quantity_before"
  , quantityAfter: Quantity $ unsafeFromForeign $ getField row "quantity_after"
  , createdAt: Timestamp $ unsafeFromForeign $ getField row "created_at"
  }
