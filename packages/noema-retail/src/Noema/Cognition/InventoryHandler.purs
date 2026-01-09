-- | Noema Handler: InventoryHandler（Arrow版）
-- |
-- | InventoryF を SQLite Storage へ解釈する Handler。
-- |
-- | ## Arrow 移行での変更点
-- |
-- | - `foldIntent` → `runIntent`
-- | - Handler の型は変わらない（f ~> m）
-- | - Intent の実行時に入力値を渡す必要がある
-- |
-- | ## 圏論的解釈
-- |
-- | Handler は A-algebra homomorphism として機能:
-- | - InventoryF は在庫操作の Functor
-- | - Handler は Intent（意志構造）を忘却し、
-- |   SQLite の状態変更という事実へ崩落させる
-- |
-- | > 実行とは忘却である。
module Noema.Cognition.InventoryHandler
  ( runInventoryIntent
  , InventoryEnv
  , Cursor
  , mkInventoryEnv
  , initializeSchema
  , interpretInventoryF
  , exec
  ) where

import Prelude

import Data.Array (head)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign, unsafeFromForeign)

import Noema.Core.Locus
  ( Timestamp(..)
  , mkTimestamp
  , currentTimestamp
  , ThingId(..)
  , SubjectId(..)
  , Quantity(..)
  , QuantityDelta(..)
  , mkSubjectId
  , unwrapSubjectId
  , unwrapQuantity
  )
import Gateway.Channel (Channel(..))
import Noema.Vorzeichnung.Vocabulary.InventoryF
  ( InventoryF(..)
  , InventoryIntent
  , StockInfo
  , SyncResult(..)
  )
import Noema.Vorzeichnung.Intent (runIntent)
import Noema.Cognition.Handler (Handler, runHandler)
import Platform.Cloudflare.FFI.SqlStorage (SqlStorage)

-- ============================================================
-- 環境
-- ============================================================

-- | Inventory Handler 環境
-- |
-- | SQLite Storage への参照を保持する。
type InventoryEnv =
  { sql :: SqlStorage
  }

-- | 環境を作成
mkInventoryEnv :: SqlStorage -> InventoryEnv
mkInventoryEnv sql = { sql }

-- | 最大在庫数（TLA+ MaxQuantity に対応）
-- |
-- | TLA+ 仕様との整合性:
-- |   CONSTANTS MaxQuantity = 1000
maxQuantity :: Int
maxQuantity = 1000

-- ============================================================
-- スキーマ初期化
-- ============================================================

-- | スキーマを初期化
-- |
-- | Durable Object の初回アクセス時に呼び出す。
initializeSchema :: SqlStorage -> Effect Unit
initializeSchema sql = do
  -- 在庫テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS inventory (
      id TEXT PRIMARY KEY,
      thing_id TEXT NOT NULL,
      subject_id TEXT NOT NULL,
      quantity INTEGER NOT NULL DEFAULT 0,
      reserved INTEGER NOT NULL DEFAULT 0,
      updated_at REAL NOT NULL,
      UNIQUE(thing_id, subject_id)
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
      FOREIGN KEY (inventory_id) REFERENCES inventory(id)
    )
  """

  -- チャネル同期テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS channel_sync (
      thing_id TEXT NOT NULL,
      channel TEXT NOT NULL,
      local_quantity INTEGER NOT NULL,
      remote_quantity INTEGER,
      sync_status TEXT NOT NULL DEFAULT 'pending',
      last_sync_at REAL,
      PRIMARY KEY (thing_id, channel)
    )
  """

  -- インデックス
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_inventory_thing ON inventory(thing_id)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_inventory_log_created ON inventory_log(created_at)"
  
  pure unit

-- ============================================================
-- Handler 実装
-- ============================================================

-- | InventoryF を Effect に解釈する Handler
-- |
-- | 圏論的解釈:
-- | この関数は自然変換 InventoryF ~> Effect を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な SQLite 実装へ変換する。
interpretInventoryF :: InventoryEnv -> Handler InventoryF Effect
interpretInventoryF env = case _ of
  GetStock (ThingId tid) sid k -> do
    let sidStr = unwrapSubjectId sid
    let cursor = execWithParams env.sql
          "SELECT * FROM inventory WHERE thing_id = ? AND subject_id = ?"
          [ unsafeToForeign tid
          , unsafeToForeign sidStr
          ]
    let maybeRow = one cursor
    let info = case maybeRow of
          Nothing -> defaultStockInfo (ThingId tid) sid
          Just row -> rowToStockInfo row
    pure (k info)

  SetStock (ThingId tid) sid qty next -> do
    now <- currentTimestamp
    let sidStr = unwrapSubjectId sid
    let inventoryId = mkInventoryId tid sidStr
    let _ = execWithParams env.sql
          """
          INSERT INTO inventory (id, thing_id, subject_id, quantity, reserved, updated_at)
          VALUES (?, ?, ?, ?, 0, ?)
          ON CONFLICT (thing_id, subject_id) DO UPDATE SET
            quantity = excluded.quantity,
            updated_at = excluded.updated_at
          """
          [ unsafeToForeign inventoryId
          , unsafeToForeign tid
          , unsafeToForeign sidStr
          , unsafeToForeign (unwrapQuantity qty)
          , unsafeToForeign (unwrap now)
          ]
    pure next

  AdjustStock (ThingId tid) sid delta k -> do
    now <- currentTimestamp
    let sidStr = unwrapSubjectId sid
    let inventoryId = mkInventoryId tid sidStr

    -- 現在の在庫を取得
    let cursor = execWithParams env.sql
          "SELECT quantity FROM inventory WHERE id = ?"
          [ unsafeToForeign inventoryId ]
    let currentQty = case one cursor of
          Nothing -> Quantity 0
          Just row -> Quantity (unsafeFromForeign (getField row "quantity"))

    let newQty = applyDelta delta currentQty

    -- 在庫を更新
    let _ = execWithParams env.sql
          "UPDATE inventory SET quantity = ?, updated_at = ? WHERE id = ?"
          [ unsafeToForeign (unwrapQuantity newQty)
          , unsafeToForeign (unwrap now)
          , unsafeToForeign inventoryId
          ]

    pure (k newQty)

  ReserveStock (ThingId tid) sid qty k -> do
    now <- currentTimestamp
    let sidStr = unwrapSubjectId sid
    let inventoryId = mkInventoryId tid sidStr

    -- 在庫確認
    let cursor = execWithParams env.sql
          "SELECT quantity, reserved FROM inventory WHERE id = ?"
          [ unsafeToForeign inventoryId ]

    case one cursor of
      Nothing -> pure (k false)
      Just row -> do
        let currentQty = unsafeFromForeign (getField row "quantity") :: Int
        let currentReserved = unsafeFromForeign (getField row "reserved") :: Int
        let available = currentQty - currentReserved
        let newReserved = currentReserved + unwrapQuantity qty

        -- TLA+ ガード:
        --   qty > 0 (Quantity は正であることを型で保証)
        --   stock[<<pid, sid>>] >= qty (available >= qty)
        --   reserved[<<pid, sid>>] + qty <= MaxQuantity
        if unwrapQuantity qty > available || newReserved > maxQuantity
          then pure (k false)
          else do
            -- reserved を更新
            let _ = execWithParams env.sql
                  "UPDATE inventory SET reserved = ?, updated_at = ? WHERE id = ?"
                  [ unsafeToForeign newReserved
                  , unsafeToForeign (unwrap now)
                  , unsafeToForeign inventoryId
                  ]
            pure (k true)

  ReleaseReservation (ThingId tid) sid _reservationId next -> do
    now <- currentTimestamp
    let sidStr = unwrapSubjectId sid
    let inventoryId = mkInventoryId tid sidStr

    -- 現在の在庫と予約を取得
    let cursor = execWithParams env.sql
          "SELECT quantity, reserved FROM inventory WHERE id = ?"
          [ unsafeToForeign inventoryId ]

    case one cursor of
      Nothing -> pure next  -- 在庫がない場合は何もしない
      Just row -> do
        let currentQty = unsafeFromForeign (getField row "quantity") :: Int
        let currentReserved = unsafeFromForeign (getField row "reserved") :: Int

        -- 予約を解放（簡略化: 全予約を解放）
        -- 実際は reservationId から qty を取得すべき
        let releaseQty = currentReserved
        let newStock = currentQty + releaseQty

        -- TLA+ ガード:
        --   stock[<<pid, sid>>] + qty <= MaxQuantity
        if newStock > maxQuantity
          then pure next  -- オーバーフロー防止: 解放しない
          else do
            let _ = execWithParams env.sql
                  "UPDATE inventory SET quantity = ?, reserved = 0, updated_at = ? WHERE id = ?"
                  [ unsafeToForeign newStock
                  , unsafeToForeign (unwrap now)
                  , unsafeToForeign inventoryId
                  ]
            pure next

  SyncToChannel channel (ThingId _tid) qty k -> do
    -- 同期ロジック（簡略化 - 実際はアダプター経由）
    pure (k (SyncSuccess { channel, quantity: qty }))

  SyncFromChannel channel (ThingId tid) k -> do
    -- 外部からの同期（簡略化）
    let defaultSid = mkSubjectId "default"
    pure (k (defaultStockInfo (ThingId tid) defaultSid))

-- ============================================================
-- Intent 実行
-- ============================================================

-- | InventoryIntent を Effect で実行
-- |
-- | Arrow 版では入力値を明示的に渡す必要がある。
-- |
-- | ```purescript
-- | -- 使用例
-- | result <- runInventoryIntent env (getStock tid lid) unit
-- | ```
runInventoryIntent :: forall a b. InventoryEnv -> InventoryIntent a b -> a -> Effect b
runInventoryIntent env intent input = 
  runIntent (interpretInventoryF env) intent input

-- ============================================================
-- ヘルパー関数
-- ============================================================

-- | 在庫 ID を生成
mkInventoryId :: String -> String -> String
mkInventoryId tid lid = tid <> ":" <> lid

-- | QuantityDelta を適用
applyDelta :: QuantityDelta -> Quantity -> Quantity
applyDelta (QuantityDelta d) (Quantity q) = Quantity (q + d)

-- | デフォルトの在庫情報
-- |
-- | 注: subjectId は Subject を表す。Thing は Subject に包摂される。
-- | 旧設計の locationId は subjectId に統合された。
defaultStockInfo :: ThingId -> SubjectId -> StockInfo
defaultStockInfo tid sid =
  { thingId: tid
  , subjectId: sid
  , quantity: Quantity 0
  , reserved: Quantity 0
  , available: Quantity 0
  }

-- | 行データを StockInfo に変換
rowToStockInfo :: Foreign -> StockInfo
rowToStockInfo row =
  let qty = unsafeFromForeign (getField row "quantity") :: Int
      reserved = unsafeFromForeign (getField row "reserved") :: Int
  in
    { thingId: ThingId (unsafeFromForeign (getField row "thing_id"))
    , subjectId: mkSubjectId (unsafeFromForeign (getField row "subject_id"))
    , quantity: Quantity qty
    , reserved: Quantity reserved
    , available: Quantity (qty - reserved)
    }

-- ============================================================
-- FFI 関数
-- ============================================================

foreign import exec :: SqlStorage -> String -> Cursor
foreign import execWithParams :: SqlStorage -> String -> Array Foreign -> Cursor
foreign import one :: Cursor -> Maybe Foreign
foreign import toArray :: Cursor -> Array Foreign
foreign import getField :: Foreign -> String -> Foreign
foreign import generateId :: Effect String

foreign import data Cursor :: Type
