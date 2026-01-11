-- | Noema Vocabulary: RetailAgencyScope（小売固有の代理範囲）
-- |
-- | noema-core の AgencyScope を小売ドメインで具体化する。
-- | AgencyScope は抽象的な String newtype であり、
-- | このモジュールが小売固有の意味を与える。
-- |
-- | ## 圏論的位置づけ
-- |
-- | AgencyScope (noema-core) は抽象的な代理範囲。
-- | RetailAgencyScope は A-algebra の解釈として具体化を提供。
-- |
-- | ## 法律的背景
-- |
-- | 代理（Agency）は民法上の重要な概念。
-- | 代理権の範囲により分類される。
-- |
-- | - 包括代理（General Agency）: 広範な代理権
-- | - 特定代理（Specific Agency）: 特定の行為のみ
-- | - 制限代理（Limited Agency）: 条件付き代理権
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | -- 代理関係を設定
-- | let scope = toAgencyScope GeneralAgency
-- |
-- | -- 抽象から具体へ復元
-- | let maybeRetail = fromAgencyScope someScope
-- | ```
module Noema.Vorzeichnung.Vocabulary.RetailAgencyScope
  ( -- * RetailAgencyScope 型
    RetailAgencyScope(..)
    -- * 変換関数
  , toAgencyScope
  , fromAgencyScope
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Noema.Vorzeichnung.Vocabulary.RelationF
  ( AgencyScope
  , mkAgencyScope
  , getAgencyScope
  )

-- ============================================================
-- RetailAgencyScope（小売固有）
-- ============================================================

-- | 小売業固有の代理範囲
-- |
-- | ActsFor 関係（代理関係）において、代理権の範囲を示す。
-- | RelationMetadata.ActsForMeta で使用される。
-- |
-- | ## 構成
-- |
-- | - GeneralAgency: 包括代理（広範な代理権を持つ）
-- | - SpecificAgency: 特定代理（特定の行為のみ代理可能）
-- | - LimitedAgency: 制限代理（条件付き代理権）
data RetailAgencyScope
  = GeneralAgency     -- ^ 包括代理
  | SpecificAgency    -- ^ 特定代理
  | LimitedAgency     -- ^ 制限代理

derive instance eqRetailAgencyScope :: Eq RetailAgencyScope

instance showRetailAgencyScope :: Show RetailAgencyScope where
  show GeneralAgency = "GeneralAgency"
  show SpecificAgency = "SpecificAgency"
  show LimitedAgency = "LimitedAgency"

-- ============================================================
-- 変換関数
-- ============================================================

-- | RetailAgencyScope を AgencyScope に変換
-- |
-- | noema-core の抽象的な AgencyScope に変換する。
-- | RelationF の ActsForMeta で使用可能になる。
toAgencyScope :: RetailAgencyScope -> AgencyScope
toAgencyScope = case _ of
  GeneralAgency ->
    mkAgencyScope "general"
  SpecificAgency ->
    mkAgencyScope "specific"
  LimitedAgency ->
    mkAgencyScope "limited"

-- | AgencyScope から RetailAgencyScope への変換
-- |
-- | 認識できない AgencyScope の場合は Nothing を返す。
-- | 他のドメインで作成された AgencyScope は
-- | 小売ドメインでは解釈できない。
fromAgencyScope :: AgencyScope -> Maybe RetailAgencyScope
fromAgencyScope as = case getAgencyScope as of
  "general" -> Just GeneralAgency
  "specific" -> Just SpecificAgency
  "limited" -> Just LimitedAgency
  _ -> Nothing
