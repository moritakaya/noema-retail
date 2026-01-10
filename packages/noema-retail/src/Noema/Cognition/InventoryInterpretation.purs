-- | Noema Cognition: InventoryInterpretation
-- |
-- | InventoryF（在庫操作語彙）を Factum（事実）へ解釈する。
-- |
-- | ## 技術的語彙からの移行
-- |
-- | 旧名称「InventoryHandler」から「InventoryInterpretation」へ変更。
-- |
-- | 理由:
-- | 1. 技術は進歩し変化するが、哲学・意味論は安定している
-- | 2. Noema の語彙体系と整合（Interpretation = 解釈）
-- | 3. 「意味→意味」の直接的対話を実現
-- |
-- | ## 役割
-- |
-- | - GetStock, SetStock 等の在庫操作を SQLite 操作に変換
-- | - FFI 境界で Effect を Factum に認識（recognize）
-- | - 分岐ロジック（在庫不足時のエラー等）を処理
-- |
-- | ## 圏論的解釈
-- |
-- | Interpretation は A-algebra homomorphism として機能:
-- | - InventoryF は在庫操作の Functor
-- | - Interpretation は Intent（意志構造）を忘却し、
-- |   SQLite の状態変更という事実へ崩落させる
-- |
-- | > 実行とは忘却である。
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | env <- recognize $ mkInventoryEnv sql
-- | result <- runInventoryIntent env someIntent unit
-- | -- result :: Factum SomeResult
-- | ```
module Noema.Cognition.InventoryInterpretation
  ( realizeInventoryIntent
  , InventoryEnv
  , Cursor
  , mkInventoryEnv
  , initializeSchema
  , interpretInventoryF
  -- FFI exports (shared with other Interpretations)
  , exec
  , execWithParams
  , one
  , toArray
  , getField
  , generateId
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign, unsafeFromForeign)

import Noema.Topos.Situs
  ( currentTimestamp
  , ThingId(..)
  , SubjectId
  , Quantity(..)
  , QuantityDelta(..)
  , mkSubjectId
  , unwrapSubjectId
  , unwrapQuantity
  )
import Noema.Vorzeichnung.Vocabulary.InventoryF
  ( InventoryF(..)
  , InventoryIntent
  , StockInfo
  , SyncResult(..)
  )
import Noema.Cognition.Interpretation (Interpretation, realizeInterpretation)
import Noema.Sedimentation.Factum (Factum, recognize)
import Platform.Cloudflare.FFI.SqlStorage (SqlStorage)

-- ============================================================
-- 環境
-- ============================================================

-- | Inventory Interpretation 環境
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
-- | FFI 境界のため Effect を返す（recognize で Factum に変換可能）。
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
-- Interpretation 実装
-- ============================================================

-- | InventoryF を Factum に解釈する Interpretation
-- |
-- | 圏論的解釈:
-- | この関数は自然変換 InventoryF ~> Factum を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な SQLite 実装へ変換する。
-- |
-- | FFI 境界での Effect は recognize で Factum に変換。
interpretInventoryF :: InventoryEnv -> Interpretation InventoryF
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
    now <- recognize currentTimestamp
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
    now <- recognize currentTimestamp
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
    now <- recognize currentTimestamp
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
    now <- recognize currentTimestamp
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
-- Intent の実現（Realization）
-- ============================================================

-- | InventoryIntent を実現する
-- |
-- | ## 哲学的基盤
-- |
-- | Husserl の「充実化」(Erfüllung):
-- | - 空虚な意志（Intent）が充実した事実（Factum）へと移行する過程
-- | - 「実行とは忘却である」：構造は消え、事実のみが残る
-- |
-- | 使用例:
-- | ```purescript
-- | result <- realizeInventoryIntent env (getStock tid sid) unit
-- | -- result :: Factum StockInfo
-- |
-- | -- エントリーポイントで Factum → Effect に変換
-- | handleFetch req = collapse do
-- |   result <- realizeInventoryIntent env intent unit
-- |   ...
-- | ```
realizeInventoryIntent :: forall a b. InventoryEnv -> InventoryIntent a b -> a -> Factum b
realizeInventoryIntent env intent input =
  realizeInterpretation (interpretInventoryF env) intent input

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
