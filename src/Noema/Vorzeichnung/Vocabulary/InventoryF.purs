-- | Noema Vocabulary: InventoryF（単項関手版・Arrow対応）
-- |
-- | 在庫操作を単項関手として定義。
-- | Arrow 制約（分岐禁止）は Intent レベルで強制される。
-- |
-- | 設計原則:
-- | - 各操作は結果型 a を持つ単項関手
-- | - 分岐を含まない純粋な操作
-- | - Presheaf Inventory : Channel^op → Set の基盤
-- |
-- | ## Monad版との違い
-- |
-- | do記法の代わりに >>> 記法を使用:
-- |
-- | ```purescript
-- | -- ❌ Monad版（分岐可能）
-- | monadicIntent = do
-- |   stock <- getStock tid lid
-- |   if stock.available > Quantity 0
-- |     then adjustStock tid lid (QuantityDelta (-1))
-- |     else pure stock
-- |
-- | -- ✅ Arrow版（分岐禁止）
-- | arrowIntent =
-- |   getStock tid lid
-- |   >>> arrIntent _.available
-- | ```
module Noema.Vorzeichnung.Vocabulary.InventoryF
  ( InventoryF(..)
  , InventoryIntent
  -- Types
  , Quantity(..)
  , QuantityDelta(..)
  , ThingId(..)
  , LocationId(..)
  , Channel(..)
  , SyncResult(..)
  , StockInfo
  -- Smart constructors
  , getStock
  , setStock
  , adjustStock
  , reserveStock
  , releaseReservation
  , syncToChannel
  , syncFromChannel
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Noema.Vorzeichnung.Intent (Intent, liftEffect, arrIntent)
import Control.Category ((>>>))

-- ============================================================
-- 基本型
-- ============================================================

-- | 物の識別子
newtype ThingId = ThingId String

derive instance eqThingId :: Eq ThingId
derive instance ordThingId :: Ord ThingId
derive newtype instance showThingId :: Show ThingId

-- | 場所の識別子
newtype LocationId = LocationId String

derive instance eqLocationId :: Eq LocationId
derive instance ordLocationId :: Ord LocationId
derive newtype instance showLocationId :: Show LocationId

-- | 数量（非負整数）
newtype Quantity = Quantity Int

derive instance Newtype Quantity _
derive instance eqQuantity :: Eq Quantity
derive instance ordQuantity :: Ord Quantity
derive newtype instance showQuantity :: Show Quantity
derive newtype instance semiringQuantity :: Semiring Quantity

-- | 数量の変化（正負あり）
newtype QuantityDelta = QuantityDelta Int

derive instance eqQuantityDelta :: Eq QuantityDelta
derive newtype instance showQuantityDelta :: Show QuantityDelta
derive newtype instance ringQuantityDelta :: Ring QuantityDelta

-- | チャネル（Presheaf の対象）
data Channel
  = Own       -- 自社（真実の源泉）
  | Smaregi   -- スマレジ POS
  | Rakuten   -- 楽天市場
  | Yahoo     -- Yahoo!ショッピング
  | Stripe    -- Stripe 決済

derive instance eqChannel :: Eq Channel
derive instance ordChannel :: Ord Channel

instance showChannel :: Show Channel where
  show Own = "Own"
  show Smaregi = "Smaregi"
  show Rakuten = "Rakuten"
  show Yahoo = "Yahoo"
  show Stripe = "Stripe"

-- | 在庫情報
type StockInfo =
  { thingId :: ThingId
  , locationId :: LocationId
  , quantity :: Quantity
  , reserved :: Quantity
  , available :: Quantity
  }

-- | 同期結果
data SyncResult
  = SyncSuccess { channel :: Channel, quantity :: Quantity }
  | SyncFailure { channel :: Channel, error :: String }

derive instance eqSyncResult :: Eq SyncResult

-- ============================================================
-- InventoryF: 単項関手としての在庫操作
-- ============================================================

-- | 在庫操作の語彙
-- |
-- | 継続渡しスタイル（CPS）で結果型を表現。
-- | これにより Functor インスタンスが自然に導出される。
-- |
-- | Arrow 制約（分岐禁止）は Intent レベルで強制される。
-- | 語彙自体は分岐の概念を持たない。
data InventoryF a
  -- | 在庫取得
  = GetStock ThingId LocationId (StockInfo -> a)
  
  -- | 在庫設定
  | SetStock ThingId LocationId Quantity a
  
  -- | 在庫調整（戻り値: 調整後の数量）
  | AdjustStock ThingId LocationId QuantityDelta (Quantity -> a)
  
  -- | 在庫予約（戻り値: 予約成功か）
  | ReserveStock ThingId LocationId Quantity (Boolean -> a)
  
  -- | 予約解放
  | ReleaseReservation ThingId LocationId String a
  
  -- | 外部チャネルへ同期
  | SyncToChannel Channel ThingId Quantity (SyncResult -> a)
  
  -- | 外部チャネルから同期
  | SyncFromChannel Channel ThingId (StockInfo -> a)

-- | Functor インスタンス
derive instance functorInventoryF :: Functor InventoryF

-- ============================================================
-- Intent 型
-- ============================================================

-- | 在庫操作の Intent
type InventoryIntent a b = Intent InventoryF a b

-- ============================================================
-- スマートコンストラクタ
-- ============================================================

-- | 在庫を取得する Intent
-- |
-- | ```purescript
-- | getStock (ThingId "SKU-001") (LocationId "LOC-001")
-- |   :: InventoryIntent Unit StockInfo
-- | ```
getStock :: ThingId -> LocationId -> InventoryIntent Unit StockInfo
getStock tid lid = liftEffect (GetStock tid lid identity)

-- | 在庫を設定する Intent
-- |
-- | ```purescript
-- | setStock (ThingId "SKU-001") (LocationId "LOC-001") (Quantity 100)
-- |   :: InventoryIntent Unit Unit
-- | ```
setStock :: ThingId -> LocationId -> Quantity -> InventoryIntent Unit Unit
setStock tid lid qty = liftEffect (SetStock tid lid qty unit)

-- | 在庫を調整する Intent
-- |
-- | ```purescript
-- | adjustStock (ThingId "SKU-001") (LocationId "LOC-001") (QuantityDelta (-1))
-- |   :: InventoryIntent Unit Quantity
-- | ```
adjustStock :: ThingId -> LocationId -> QuantityDelta -> InventoryIntent Unit Quantity
adjustStock tid lid delta = liftEffect (AdjustStock tid lid delta identity)

-- | 在庫を予約する Intent
-- |
-- | ```purescript
-- | reserveStock (ThingId "SKU-001") (LocationId "LOC-001") (Quantity 5)
-- |   :: InventoryIntent Unit Boolean
-- | ```
reserveStock :: ThingId -> LocationId -> Quantity -> InventoryIntent Unit Boolean
reserveStock tid lid qty = liftEffect (ReserveStock tid lid qty identity)

-- | 予約を解放する Intent
releaseReservation :: ThingId -> LocationId -> String -> InventoryIntent Unit Unit
releaseReservation tid lid rid = liftEffect (ReleaseReservation tid lid rid unit)

-- | 外部チャネルへ同期する Intent
syncToChannel :: Channel -> ThingId -> Quantity -> InventoryIntent Unit SyncResult
syncToChannel ch tid qty = liftEffect (SyncToChannel ch tid qty identity)

-- | 外部チャネルから同期する Intent
syncFromChannel :: Channel -> ThingId -> InventoryIntent Unit StockInfo
syncFromChannel ch tid = liftEffect (SyncFromChannel ch tid identity)

-- ============================================================
-- Arrow 合成例（分岐なし）
-- ============================================================

-- | 注文処理: 在庫確認 → 予約
-- |
-- | ```purescript
-- | processOrder :: ThingId -> LocationId -> Quantity -> InventoryIntent Unit Boolean
-- | processOrder tid lid qty =
-- |   getStock tid lid
-- |   >>> arrIntent (\info -> info.available >= qty)
-- |   -- 注: この時点で分岐はできない！
-- |   -- 結果は Boolean として返され、分岐は Handler 層で処理
-- | ```

-- | 在庫同期: 取得 → チャネルへ送信
-- |
-- | ```purescript
-- | syncInventory :: ThingId -> LocationId -> Channel -> InventoryIntent Unit SyncResult
-- | syncInventory tid lid ch =
-- |   getStock tid lid
-- |   >>> arrIntent _.quantity
-- |   >>> (\qty -> syncToChannel ch tid qty)  -- 注: これは関数適用、分岐ではない
-- | ```
-- |
-- | 上記は実際には以下のように書く必要がある（カリー化の制約）:
-- |
-- | ```purescript
-- | syncInventoryFixed :: ThingId -> LocationId -> Channel -> InventoryIntent Unit StockInfo
-- | syncInventoryFixed tid lid ch =
-- |   getStock tid lid
-- |   -- syncToChannel は Quantity を入力として期待するが、
-- |   -- getStock は StockInfo を返す。
-- |   -- これは Intent の合成で解決。
-- | ```

-- ============================================================
-- 違法な Intent（型エラーになる）
-- ============================================================

-- | 以下のコードは型エラーになる（ArrowChoice がないため）
-- |
-- | ```purescript
-- | illegalBranching :: ThingId -> LocationId -> InventoryIntent Unit Unit
-- | illegalBranching tid lid =
-- |   getStock tid lid
-- |   >>> arrIntent (\info -> 
-- |         if info.available > Quantity 0 
-- |         then Left () 
-- |         else Right ())
-- |   >>> left (adjustStock tid lid (QuantityDelta (-1)))  -- 型エラー!
-- | ```
-- |
-- | 分岐が必要な場合は Handler（Cognition）層で処理する。
