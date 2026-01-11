-- | Noema Vocabulary: RetailSecurityType（小売固有の担保権種別）
-- |
-- | noema-core の SecurityType を小売ドメインで具体化する。
-- | SecurityType は抽象的な String newtype であり、
-- | このモジュールが小売固有の意味を与える。
-- |
-- | ## 圏論的位置づけ
-- |
-- | SecurityType (noema-core) は抽象的な担保権種別。
-- | RetailSecurityType は A-algebra の解釈として具体化を提供。
-- |
-- | ## 法律的背景
-- |
-- | 担保権（Security Interest）は法体系によって分類が異なる。
-- | 本モジュールは日本民法・商法に基づく分類を提供。
-- |
-- | - 質権（Pledge）: 民法342条〜
-- | - 留置権（Lien）: 民法295条〜
-- | - 抵当権（Mortgage）: 民法369条〜
-- | - 譲渡担保（Security Interest）: 判例法理
-- | - 所有権留保（Retention of Title）: 商取引慣行
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | -- 質権を設定
-- | let securityType = toSecurityType Pledge
-- |
-- | -- 抽象から具体へ復元
-- | let maybeRetail = fromSecurityType someSecurityType
-- | ```
module Noema.Vorzeichnung.Vocabulary.RetailSecurityType
  ( -- * RetailSecurityType 型
    RetailSecurityType(..)
    -- * 変換関数
  , toSecurityType
  , fromSecurityType
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Noema.Vorzeichnung.Vocabulary.RelationF
  ( SecurityType
  , mkSecurityType
  , getSecurityType
  )

-- ============================================================
-- RetailSecurityType（小売固有）
-- ============================================================

-- | 小売業固有の担保権種別
-- |
-- | 日本民法・商法に基づく担保権の分類。
-- | RelationMetadata.SecuresMeta で使用される。
-- |
-- | ## 構成
-- |
-- | - Pledge: 質権（動産・債権を担保に供する）
-- | - Lien: 留置権（債務履行まで物を留置する）
-- | - Mortgage: 抵当権（不動産を担保に供する）
-- | - SecurityInterest: 譲渡担保（所有権を移転して担保とする）
-- | - RetentionOfTitle: 所有権留保（代金完済まで所有権を留保）
data RetailSecurityType
  = Pledge            -- ^ 質権
  | Lien              -- ^ 留置権
  | Mortgage          -- ^ 抵当権
  | SecurityInterest  -- ^ 譲渡担保
  | RetentionOfTitle  -- ^ 所有権留保

derive instance eqRetailSecurityType :: Eq RetailSecurityType

instance showRetailSecurityType :: Show RetailSecurityType where
  show Pledge = "Pledge"
  show Lien = "Lien"
  show Mortgage = "Mortgage"
  show SecurityInterest = "SecurityInterest"
  show RetentionOfTitle = "RetentionOfTitle"

-- ============================================================
-- 変換関数
-- ============================================================

-- | RetailSecurityType を SecurityType に変換
-- |
-- | noema-core の抽象的な SecurityType に変換する。
-- | RelationF の SecuresMeta で使用可能になる。
toSecurityType :: RetailSecurityType -> SecurityType
toSecurityType = case _ of
  Pledge ->
    mkSecurityType "pledge"
  Lien ->
    mkSecurityType "lien"
  Mortgage ->
    mkSecurityType "mortgage"
  SecurityInterest ->
    mkSecurityType "security_interest"
  RetentionOfTitle ->
    mkSecurityType "retention_of_title"

-- | SecurityType から RetailSecurityType への変換
-- |
-- | 認識できない SecurityType の場合は Nothing を返す。
-- | 他の法体系（例：UCC, 英国法）で作成された SecurityType は
-- | 日本法ベースの小売ドメインでは解釈できない。
fromSecurityType :: SecurityType -> Maybe RetailSecurityType
fromSecurityType st = case getSecurityType st of
  "pledge" -> Just Pledge
  "lien" -> Just Lien
  "mortgage" -> Just Mortgage
  "security_interest" -> Just SecurityInterest
  "retention_of_title" -> Just RetentionOfTitle
  _ -> Nothing
