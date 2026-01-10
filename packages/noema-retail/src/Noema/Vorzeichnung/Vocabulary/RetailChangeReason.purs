-- | Noema Vocabulary: RetailChangeReason（小売固有の位置変更理由）
-- |
-- | noema-core の ChangeReason を小売ドメインで具体化する。
-- | ChangeReason は抽象的な Json newtype であり、
-- | このモジュールが小売固有の意味を与える。
-- |
-- | ## 圏論的位置づけ
-- |
-- | ChangeReason (noema-core) は抽象的な位置変更理由。
-- | RetailChangeReason は A-algebra の解釈として具体化を提供。
-- |
-- | ```
-- | ChangeReason (抽象)   RetailChangeReason (具体)
-- |        │                     │
-- |        │   fromChangeReason  │
-- |        │ <──────────────────│
-- |        │                     │
-- |        │   toChangeReason    │
-- |        │ ──────────────────> │
-- |        │                     │
-- |        ▼                     ▼
-- |   Json newtype           ADT (Sale, Purchase, ...)
-- | ```
module Noema.Vorzeichnung.Vocabulary.RetailChangeReason
  ( -- * RetailChangeReason 型
    RetailChangeReason(..)
    -- * 変換関数
  , toChangeReason
  , fromChangeReason
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Noema.Topos.Situs (ContractId)
import Noema.Vorzeichnung.Vocabulary.ThingF
  ( ChangeReason
  , mkChangeReason
  , getReasonType
  , getReasonDetail
  , getReasonContractId
  )

-- ============================================================
-- RetailChangeReason（小売固有）
-- ============================================================

-- | 小売業固有の位置変更理由
-- |
-- | Situs（位置）が変更された理由を小売ドメインで表現。
-- |
-- | ## 構成
-- |
-- | - Sale: 販売により所有権移転
-- | - Purchase: 仕入れにより所有権取得
-- | - Transfer: 内部移動（倉庫間、店舗間）
-- | - Return: 返品による所有権移転
-- | - Adjustment: 棚卸調整（理由を文字列で記録）
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | -- 販売による移動
-- | let reason = Sale contractId
-- |     cr = toChangeReason reason
-- |
-- | -- ChangeReason から復元
-- | let maybeReason = fromChangeReason cr
-- | ```
data RetailChangeReason
  = Sale ContractId       -- ^ 販売（所有権移転）
  | Purchase ContractId   -- ^ 仕入れ（所有権取得）
  | Transfer              -- ^ 内部移動
  | Return ContractId     -- ^ 返品
  | Adjustment String     -- ^ 棚卸調整（理由）

derive instance eqRetailChangeReason :: Eq RetailChangeReason

instance showRetailChangeReason :: Show RetailChangeReason where
  show (Sale cid) = "(Sale " <> show cid <> ")"
  show (Purchase cid) = "(Purchase " <> show cid <> ")"
  show Transfer = "Transfer"
  show (Return cid) = "(Return " <> show cid <> ")"
  show (Adjustment reason) = "(Adjustment " <> reason <> ")"

-- ============================================================
-- 変換関数
-- ============================================================

-- | RetailChangeReason を ChangeReason に変換
-- |
-- | noema-core の抽象的な ChangeReason に変換する。
-- | ThingF の SitusChange で使用可能になる。
toChangeReason :: RetailChangeReason -> ChangeReason
toChangeReason = case _ of
  Sale cid ->
    mkChangeReason "sale" Nothing (Just cid)
  Purchase cid ->
    mkChangeReason "purchase" Nothing (Just cid)
  Transfer ->
    mkChangeReason "transfer" Nothing Nothing
  Return cid ->
    mkChangeReason "return" Nothing (Just cid)
  Adjustment reason ->
    mkChangeReason "adjustment" (Just reason) Nothing

-- | ChangeReason から RetailChangeReason への変換
-- |
-- | 認識できない ChangeReason の場合は Nothing を返す。
-- | 他のドメイン（例：金融、物流）で作成された ChangeReason は
-- | 小売ドメインでは解釈できない。
fromChangeReason :: ChangeReason -> Maybe RetailChangeReason
fromChangeReason cr = case getReasonType cr of
  "sale" -> do
    cid <- getReasonContractId cr
    pure (Sale cid)
  "purchase" -> do
    cid <- getReasonContractId cr
    pure (Purchase cid)
  "transfer" ->
    Just Transfer
  "return" -> do
    cid <- getReasonContractId cr
    pure (Return cid)
  "adjustment" ->
    Adjustment <$> getReasonDetail cr
  _ ->
    Nothing
