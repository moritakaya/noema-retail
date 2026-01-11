-- | Noema Vocabulary: RetailChangeType（小売固有の変更種別）
-- |
-- | noema-core の ChangeType を小売ドメインで具体化する。
-- | ChangeType は抽象的な String newtype であり、
-- | このモジュールが小売固有の意味を与える。
-- |
-- | ## 圏論的位置づけ
-- |
-- | ChangeType (noema-core) は抽象的な変更通知種別。
-- | RetailChangeType は A-algebra の解釈として具体化を提供。
-- |
-- | ```
-- | ChangeType (抽象)   RetailChangeType (具体)
-- |        │                     │
-- |        │   fromChangeType    │
-- |        │ <──────────────────│
-- |        │                     │
-- |        │   toChangeType      │
-- |        │ ──────────────────> │
-- |        │                     │
-- |        ▼                     ▼
-- |   String newtype         ADT (PriceChanged, ...)
-- | ```
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | -- 小売ドメインでの使用
-- | let notifyOn = [PriceChanged, AvailabilityChanged]
-- |     changeTypes = map toChangeType notifyOn
-- |
-- | -- 抽象から具体へ復元
-- | let maybeRetail = fromChangeType someChangeType
-- | ```
module Noema.Vorzeichnung.Vocabulary.RetailChangeType
  ( -- * RetailChangeType 型
    RetailChangeType(..)
    -- * 変換関数
  , toChangeType
  , fromChangeType
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Noema.Vorzeichnung.Vocabulary.RelationF
  ( ChangeType
  , mkChangeType
  , getChangeType
  )

-- ============================================================
-- RetailChangeType（小売固有）
-- ============================================================

-- | 小売業固有の変更通知種別
-- |
-- | Thing の状態変更を監視する際に、通知すべき変更の種類を指定する。
-- | IntendsMeta の notifyOn フィールドで使用される。
-- |
-- | ## 構成
-- |
-- | - PriceChanged: 価格が変更された
-- | - AvailabilityChanged: 在庫可用性が変更された
-- | - PropertyChanged: 属性（色、サイズ等）が変更された
-- | - Discontinued: 商品が廃盤になった
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | -- 価格と在庫変更を監視
-- | let intendsMeta = IntendsMeta
-- |       { quantity: mkQuantity 5
-- |       , notifyOn: map toChangeType [PriceChanged, AvailabilityChanged]
-- |       }
-- | ```
data RetailChangeType
  = PriceChanged           -- ^ 価格変更
  | AvailabilityChanged    -- ^ 在庫可用性変更
  | PropertyChanged        -- ^ 属性変更
  | Discontinued           -- ^ 廃盤

derive instance eqRetailChangeType :: Eq RetailChangeType

instance showRetailChangeType :: Show RetailChangeType where
  show PriceChanged = "PriceChanged"
  show AvailabilityChanged = "AvailabilityChanged"
  show PropertyChanged = "PropertyChanged"
  show Discontinued = "Discontinued"

-- ============================================================
-- 変換関数
-- ============================================================

-- | RetailChangeType を ChangeType に変換
-- |
-- | noema-core の抽象的な ChangeType に変換する。
-- | RelationF の IntendsMeta で使用可能になる。
toChangeType :: RetailChangeType -> ChangeType
toChangeType = case _ of
  PriceChanged ->
    mkChangeType "price_changed"
  AvailabilityChanged ->
    mkChangeType "availability_changed"
  PropertyChanged ->
    mkChangeType "property_changed"
  Discontinued ->
    mkChangeType "discontinued"

-- | ChangeType から RetailChangeType への変換
-- |
-- | 認識できない ChangeType の場合は Nothing を返す。
-- | 他のドメイン（例：製造、物流）で作成された ChangeType は
-- | 小売ドメインでは解釈できない。
fromChangeType :: ChangeType -> Maybe RetailChangeType
fromChangeType ct = case getChangeType ct of
  "price_changed" -> Just PriceChanged
  "availability_changed" -> Just AvailabilityChanged
  "property_changed" -> Just PropertyChanged
  "discontinued" -> Just Discontinued
  _ -> Nothing
