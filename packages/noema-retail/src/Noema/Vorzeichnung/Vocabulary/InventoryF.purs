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
-- | ## 設計変更: LocationId → SubjectId
-- |
-- | 旧設計では LocationId（倉庫、店舗）が在庫の位置を表していた。
-- | 新設計では Subject が Thing を包摂し、
-- | その Subject の位置が Thing の位置を決定する。
-- |
-- | ## Monad版との違い
-- |
-- | do記法の代わりに >>> 記法を使用:
-- |
-- | ```purescript
-- | -- ❌ Monad版（分岐可能）
-- | monadicIntent = do
-- |   stock <- getStock tid sid
-- |   if stock.available > Quantity 0
-- |     then adjustStock tid sid (QuantityDelta (-1))
-- |     else pure stock
-- |
-- | -- ✅ Arrow版（分岐禁止）
-- | arrowIntent =
-- |   getStock tid sid
-- |   >>> arrIntent _.available
-- | ```
module Noema.Vorzeichnung.Vocabulary.InventoryF
  ( InventoryF(..)
  , InventoryIntent
  -- Types (re-exported from Core/Locus)
  , module Noema.Core.Locus
  -- Types (re-exported from Gateway)
  , module Gateway.Channel
  , module Gateway.InventoryAdapter
  -- Local types
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

import Noema.Vorzeichnung.Intent (Intent, liftEffect)
import Noema.Core.Locus (ThingId(..), SubjectId(..), Quantity(..), QuantityDelta(..), mkThingId, mkSubjectId, unwrapThingId, unwrapSubjectId, mkQuantity, unwrapQuantity, mkQuantityDelta, unwrapQuantityDelta)
import Gateway.Channel (Channel(..))
import Gateway.InventoryAdapter (SyncResult(..))

-- ============================================================
-- 在庫情報
-- ============================================================

-- | 在庫情報
-- |
-- | subjectId は Subject（倉庫、店舗など）を表す。Thing は Subject に包摂される。
-- | 旧設計の locationId は subjectId に統合された。
type StockInfo =
  { thingId :: ThingId
  , subjectId :: SubjectId  -- 旧: locationId
  , quantity :: Quantity
  , reserved :: Quantity
  , available :: Quantity
  }

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
-- |
-- | 注: LocationId は SubjectId に統合された。
-- | SubjectId は Subject を表す。Thing は Subject に包摂される。
data InventoryF a
  -- | 在庫取得
  = GetStock ThingId SubjectId (StockInfo -> a)

  -- | 在庫設定
  | SetStock ThingId SubjectId Quantity a

  -- | 在庫調整（戻り値: 調整後の数量）
  | AdjustStock ThingId SubjectId QuantityDelta (Quantity -> a)

  -- | 在庫予約（戻り値: 予約成功か）
  | ReserveStock ThingId SubjectId Quantity (Boolean -> a)

  -- | 予約解放
  | ReleaseReservation ThingId SubjectId String a

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
-- | getStock (ThingId "SKU-001") (SubjectId (LocusId "warehouse-001"))
-- |   :: InventoryIntent Unit StockInfo
-- | ```
getStock :: ThingId -> SubjectId -> InventoryIntent Unit StockInfo
getStock tid sid = liftEffect (GetStock tid sid identity)

-- | 在庫を設定する Intent
-- |
-- | ```purescript
-- | setStock (ThingId "SKU-001") (mkSubjectId "warehouse-001") (Quantity 100)
-- |   :: InventoryIntent Unit Unit
-- | ```
setStock :: ThingId -> SubjectId -> Quantity -> InventoryIntent Unit Unit
setStock tid sid qty = liftEffect (SetStock tid sid qty unit)

-- | 在庫を調整する Intent
-- |
-- | ```purescript
-- | adjustStock (ThingId "SKU-001") (mkSubjectId "warehouse-001") (QuantityDelta (-1))
-- |   :: InventoryIntent Unit Quantity
-- | ```
adjustStock :: ThingId -> SubjectId -> QuantityDelta -> InventoryIntent Unit Quantity
adjustStock tid sid delta = liftEffect (AdjustStock tid sid delta identity)

-- | 在庫を予約する Intent
-- |
-- | ```purescript
-- | reserveStock (ThingId "SKU-001") (mkSubjectId "warehouse-001") (Quantity 5)
-- |   :: InventoryIntent Unit Boolean
-- | ```
reserveStock :: ThingId -> SubjectId -> Quantity -> InventoryIntent Unit Boolean
reserveStock tid sid qty = liftEffect (ReserveStock tid sid qty identity)

-- | 予約を解放する Intent
releaseReservation :: ThingId -> SubjectId -> String -> InventoryIntent Unit Unit
releaseReservation tid sid rid = liftEffect (ReleaseReservation tid sid rid unit)

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
-- | processOrder :: ThingId -> SubjectId -> Quantity -> InventoryIntent Unit Boolean
-- | processOrder tid sid qty =
-- |   getStock tid sid
-- |   >>> arrIntent (\info -> info.available >= qty)
-- |   -- 注: この時点で分岐はできない！
-- |   -- 結果は Boolean として返され、分岐は Handler 層で処理
-- | ```

-- | 在庫同期: 取得 → チャネルへ送信
-- |
-- | ```purescript
-- | syncInventory :: ThingId -> SubjectId -> Channel -> InventoryIntent Unit SyncResult
-- | syncInventory tid sid ch =
-- |   getStock tid sid
-- |   >>> arrIntent _.quantity
-- |   >>> (\qty -> syncToChannel ch tid qty)  -- 注: これは関数適用、分岐ではない
-- | ```
-- |
-- | 上記は実際には以下のように書く必要がある（カリー化の制約）:
-- |
-- | ```purescript
-- | syncInventoryFixed :: ThingId -> SubjectId -> Channel -> InventoryIntent Unit StockInfo
-- | syncInventoryFixed tid sid ch =
-- |   getStock tid sid
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
-- | illegalBranching :: ThingId -> SubjectId -> InventoryIntent Unit Unit
-- | illegalBranching tid sid =
-- |   getStock tid sid
-- |   >>> arrIntent (\info ->
-- |         if info.available > Quantity 0
-- |         then Left ()
-- |         else Right ())
-- |   >>> left (adjustStock tid sid (QuantityDelta (-1)))  -- 型エラー!
-- | ```
-- |
-- | 分岐が必要な場合は Handler（Cognition）層で処理する。
