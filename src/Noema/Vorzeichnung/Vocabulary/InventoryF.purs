-- | Noema Vocabulary: InventoryF（二項関手版）
-- |
-- | 在庫操作を二項関手として定義。
-- | Arrow ベースの Intent に対応する語彙。
-- |
-- | 設計原則:
-- | - 各操作は入力型 i と出力型 o を明示
-- | - 分岐を含まない純粋な操作
-- | - Presheaf Inventory : Channel^op → Set の基盤
module Noema.Vorzeichnung.Vocabulary.InventoryF
  ( InventoryF(..)
  , Quantity(..)
  , QuantityDelta(..)
  , ThingId(..)
  , LocationId(..)
  , Channel(..)
  , SyncResult(..)
  , StockInfo(..)
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

import Data.Tuple (Tuple(..))
import Data.Maybe (Maybe)
import Noema.Vorzeichnung.Intent (Intent', liftEffect, arrIntent, (>>>))

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
-- InventoryF: 二項関手としての在庫操作
-- ============================================================

-- | 在庫操作の語彙
-- |
-- | 各操作は入力型 i と出力型 o を持つ二項関手。
-- | これにより Arrow として合成可能になる。
-- |
-- | 圏論的解釈:
-- | InventoryF : Type × Type → Type
-- | (i, o) ↦ InventoryF i o
data InventoryF i o
  -- | 在庫取得: () → StockInfo
  = GetStock ThingId LocationId (i -> Unit) (StockInfo -> o)
  
  -- | 在庫設定: Quantity → ()
  | SetStock ThingId LocationId (i -> Quantity) (Unit -> o)
  
  -- | 在庫調整: QuantityDelta → Quantity（調整後の数量）
  | AdjustStock ThingId LocationId (i -> QuantityDelta) (Quantity -> o)
  
  -- | 在庫予約: Quantity → Boolean（予約成功か）
  | ReserveStock ThingId LocationId (i -> Quantity) (Boolean -> o)
  
  -- | 予約解放: () → ()
  | ReleaseReservation ThingId LocationId String (i -> Unit) (Unit -> o)
  
  -- | 外部チャネルへ同期: Quantity → SyncResult
  | SyncToChannel Channel ThingId (i -> Quantity) (SyncResult -> o)
  
  -- | 外部チャネルから同期: () → StockInfo
  | SyncFromChannel Channel ThingId (i -> Unit) (StockInfo -> o)

-- | Profunctor インスタンス
-- | dimap f g (InventoryF ...) で入出力の型を変換
instance profunctorInventoryF :: Profunctor InventoryF where
  dimap f g (GetStock tid lid fi fo) = 
    GetStock tid lid (fi <<< f) (g <<< fo)
  dimap f g (SetStock tid lid fi fo) = 
    SetStock tid lid (fi <<< f) (g <<< fo)
  dimap f g (AdjustStock tid lid fi fo) = 
    AdjustStock tid lid (fi <<< f) (g <<< fo)
  dimap f g (ReserveStock tid lid fi fo) = 
    ReserveStock tid lid (fi <<< f) (g <<< fo)
  dimap f g (ReleaseReservation tid lid rid fi fo) = 
    ReleaseReservation tid lid rid (fi <<< f) (g <<< fo)
  dimap f g (SyncToChannel ch tid fi fo) = 
    SyncToChannel ch tid (fi <<< f) (g <<< fo)
  dimap f g (SyncFromChannel ch tid fi fo) = 
    SyncFromChannel ch tid (fi <<< f) (g <<< fo)

-- ============================================================
-- スマートコンストラクタ
-- ============================================================

-- | 在庫を取得する Intent
getStock :: ThingId -> LocationId -> Intent' InventoryF Unit StockInfo
getStock tid lid = liftEffect (GetStock tid lid identity identity)

-- | 在庫を設定する Intent
setStock :: ThingId -> LocationId -> Intent' InventoryF Quantity Unit
setStock tid lid = liftEffect (SetStock tid lid identity identity)

-- | 在庫を調整する Intent
adjustStock :: ThingId -> LocationId -> Intent' InventoryF QuantityDelta Quantity
adjustStock tid lid = liftEffect (AdjustStock tid lid identity identity)

-- | 在庫を予約する Intent
reserveStock :: ThingId -> LocationId -> Intent' InventoryF Quantity Boolean
reserveStock tid lid = liftEffect (ReserveStock tid lid identity identity)

-- | 予約を解放する Intent
releaseReservation :: ThingId -> LocationId -> String -> Intent' InventoryF Unit Unit
releaseReservation tid lid rid = liftEffect (ReleaseReservation tid lid rid identity identity)

-- | 外部チャネルへ同期する Intent
syncToChannel :: Channel -> ThingId -> Intent' InventoryF Quantity SyncResult
syncToChannel ch tid = liftEffect (SyncToChannel ch tid identity identity)

-- | 外部チャネルから同期する Intent
syncFromChannel :: Channel -> ThingId -> Intent' InventoryF Unit StockInfo
syncFromChannel ch tid = liftEffect (SyncFromChannel ch tid identity identity)

-- ============================================================
-- Intent の合成例（分岐なし）
-- ============================================================

-- | 注文処理: 在庫確認 → 予約 → 調整
-- |
-- | これは合法な Intent:
-- | - 線形な合成のみ
-- | - 分岐なし
-- | - 構造が静的に確定
-- processOrder :: ThingId -> LocationId -> Quantity -> Intent' InventoryF Unit Boolean
-- processOrder tid lid qty =
--   arrIntent (const qty) 
--   >>> reserveStock tid lid

-- | 在庫同期: 取得 → チャネルへ送信
-- |
-- | これも合法:
-- | - getStock の結果を syncToChannel に渡す
-- | - 分岐なし
-- syncInventory :: ThingId -> LocationId -> Channel -> Intent' InventoryF Unit SyncResult
-- syncInventory tid lid ch =
--   getStock tid lid
--   >>> arrIntent (\info -> info.quantity)
--   >>> syncToChannel ch tid

-- ============================================================
-- 違法な Intent（型エラーになる）
-- ============================================================

-- | 以下のコードは型エラーになる（ArrowChoice がないため）
-- |
-- | illegalBranching :: ThingId -> LocationId -> Intent' InventoryF Unit Unit
-- | illegalBranching tid lid =
-- |   getStock tid lid
-- |   >>> arrIntent (\info -> if info.available > Quantity 0 then Left () else Right ())
-- |   >>> left (adjustStock tid lid)  -- 型エラー: No instance for ArrowChoice
-- |
-- | 分岐が必要な場合は、Handler（Cognition）の層で処理する。
