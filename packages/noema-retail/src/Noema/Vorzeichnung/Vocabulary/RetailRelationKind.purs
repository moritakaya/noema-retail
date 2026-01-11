-- | Noema Vocabulary: RetailRelationKind（小売固有の関係種別）
-- |
-- | noema-core の RelationKind を小売ドメインで具体化する。
-- | RelationKind は抽象的な Json newtype であり、
-- | このモジュールが小売固有の意味を与える。
-- |
-- | ## 圏論的位置づけ
-- |
-- | RelationKind (noema-core) は抽象的な関係種別。
-- | RetailRelationKind は A-algebra の解釈として具体化を提供。
-- |
-- | ```
-- | RelationKind (抽象)   RetailRelationKind (具体)
-- |        │                     │
-- |        │   fromRelationKind  │
-- |        │ <──────────────────│
-- |        │                     │
-- |        │   toRelationKind    │
-- |        │ ──────────────────> │
-- |        │                     │
-- |        ▼                     ▼
-- |   Json newtype           ADT (Owns, Reserves, ...)
-- | ```
-- |
-- | ## カテゴリ
-- |
-- | - spatial: 空間的関係（包摂）
-- | - rights: 権利関係（所有、占有等）
-- | - temporal: 時間的関係（引当）
-- | - transitive: 過渡的関係（移動）
-- | - structural: 構造的関係（構成）
-- | - cognitive: 認識的関係（観測）
-- | - performative: 行為的関係（代理）
-- | - negative: 消極的関係（制限）
module Noema.Vorzeichnung.Vocabulary.RetailRelationKind
  ( -- * RetailRelationKind 型
    RetailRelationKind(..)
    -- * 変換関数
  , toRelationKind
  , fromRelationKind
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Noema.Vorzeichnung.Vocabulary.RelationF
  ( RelationKind
  , mkRelationKind
  , getRelationKindType
  )

-- ============================================================
-- RetailRelationKind（小売固有）
-- ============================================================

-- | 小売業固有の関係種別
-- |
-- | Subject と Thing 間の関係を小売ドメインで表現。
-- |
-- | ## 構成
-- |
-- | ### 空間的関係 (spatial)
-- | - Contains: 物理的包含
-- | - Guards: 保管・監視
-- |
-- | ### 権利関係 (rights)
-- | - Owns: 所有権
-- | - Possesses: 占有
-- | - Claims: 請求権
-- | - Secures: 担保権
-- | - SharedBy: 共有
-- |
-- | ### 時間的関係 (temporal)
-- | - Reserves: 引当（在庫予約）
-- | - Commits: 確約
-- | - Intends: 意図（購入意思）
-- |
-- | ### 過渡的関係 (transitive)
-- | - Transports: 輸送中
-- | - Consigns: 委託
-- |
-- | ### 構造的関係 (structural)
-- | - ComposedOf: 構成要素
-- | - BundledWith: バンドル
-- | - Substitutes: 代替品
-- |
-- | ### 認識的関係 (cognitive)
-- | - Observes: 観測
-- | - Tracks: 追跡
-- |
-- | ### 行為的関係 (performative)
-- | - ActsFor: 代理
-- |
-- | ### 消極的関係 (negative)
-- | - Restricts: 制限
data RetailRelationKind
  -- 空間的関係 (spatial)
  = Contains           -- ^ 物理的包含
  | Guards             -- ^ 保管・監視
  -- 権利関係 (rights)
  | Owns               -- ^ 所有権
  | Possesses          -- ^ 占有
  | Claims             -- ^ 請求権
  | Secures            -- ^ 担保権
  | SharedBy           -- ^ 共有
  -- 時間的関係 (temporal)
  | Reserves           -- ^ 引当（在庫予約）
  | Commits            -- ^ 確約
  | Intends            -- ^ 意図（購入意思）
  -- 過渡的関係 (transitive)
  | Transports         -- ^ 輸送中
  | Consigns           -- ^ 委託
  -- 構造的関係 (structural)
  | ComposedOf         -- ^ 構成要素
  | BundledWith        -- ^ バンドル
  | Substitutes        -- ^ 代替品
  -- 認識的関係 (cognitive)
  | Observes           -- ^ 観測
  | Tracks             -- ^ 追跡
  -- 行為的関係 (performative)
  | ActsFor            -- ^ 代理
  -- 消極的関係 (negative)
  | Restricts          -- ^ 制限

derive instance eqRetailRelationKind :: Eq RetailRelationKind

instance showRetailRelationKind :: Show RetailRelationKind where
  show Contains = "Contains"
  show Guards = "Guards"
  show Owns = "Owns"
  show Possesses = "Possesses"
  show Claims = "Claims"
  show Secures = "Secures"
  show SharedBy = "SharedBy"
  show Reserves = "Reserves"
  show Commits = "Commits"
  show Intends = "Intends"
  show Transports = "Transports"
  show Consigns = "Consigns"
  show ComposedOf = "ComposedOf"
  show BundledWith = "BundledWith"
  show Substitutes = "Substitutes"
  show Observes = "Observes"
  show Tracks = "Tracks"
  show ActsFor = "ActsFor"
  show Restricts = "Restricts"

-- ============================================================
-- 変換関数
-- ============================================================

-- | RetailRelationKind を RelationKind に変換
-- |
-- | noema-core の抽象的な RelationKind に変換する。
-- | RelationF の Relation で使用可能になる。
toRelationKind :: RetailRelationKind -> RelationKind
toRelationKind = case _ of
  -- 空間的関係 (spatial)
  Contains ->
    mkRelationKind "contains" "spatial" Nothing
  Guards ->
    mkRelationKind "guards" "spatial" Nothing
  -- 権利関係 (rights)
  Owns ->
    mkRelationKind "owns" "rights" Nothing
  Possesses ->
    mkRelationKind "possesses" "rights" Nothing
  Claims ->
    mkRelationKind "claims" "rights" Nothing
  Secures ->
    mkRelationKind "secures" "rights" Nothing
  SharedBy ->
    mkRelationKind "shared_by" "rights" Nothing
  -- 時間的関係 (temporal)
  Reserves ->
    mkRelationKind "reserves" "temporal" Nothing
  Commits ->
    mkRelationKind "commits" "temporal" Nothing
  Intends ->
    mkRelationKind "intends" "temporal" Nothing
  -- 過渡的関係 (transitive)
  Transports ->
    mkRelationKind "transports" "transitive" Nothing
  Consigns ->
    mkRelationKind "consigns" "transitive" Nothing
  -- 構造的関係 (structural)
  ComposedOf ->
    mkRelationKind "composed_of" "structural" Nothing
  BundledWith ->
    mkRelationKind "bundled_with" "structural" Nothing
  Substitutes ->
    mkRelationKind "substitutes" "structural" Nothing
  -- 認識的関係 (cognitive)
  Observes ->
    mkRelationKind "observes" "cognitive" Nothing
  Tracks ->
    mkRelationKind "tracks" "cognitive" Nothing
  -- 行為的関係 (performative)
  ActsFor ->
    mkRelationKind "acts_for" "performative" Nothing
  -- 消極的関係 (negative)
  Restricts ->
    mkRelationKind "restricts" "negative" Nothing

-- | RelationKind から RetailRelationKind への変換
-- |
-- | 認識できない RelationKind の場合は Nothing を返す。
-- | 他のドメイン（例：金融、製造）で作成された RelationKind は
-- | 小売ドメインでは解釈できない。
fromRelationKind :: RelationKind -> Maybe RetailRelationKind
fromRelationKind rk = case getRelationKindType rk of
  -- 空間的関係
  "contains" -> Just Contains
  "containment" -> Just Contains  -- noema-core の containmentKind と互換
  "guards" -> Just Guards
  -- 権利関係
  "owns" -> Just Owns
  "possesses" -> Just Possesses
  "claims" -> Just Claims
  "secures" -> Just Secures
  "shared_by" -> Just SharedBy
  -- 時間的関係
  "reserves" -> Just Reserves
  "commits" -> Just Commits
  "intends" -> Just Intends
  -- 過渡的関係
  "transports" -> Just Transports
  "consigns" -> Just Consigns
  -- 構造的関係
  "composed_of" -> Just ComposedOf
  "bundled_with" -> Just BundledWith
  "substitutes" -> Just Substitutes
  -- 認識的関係
  "observes" -> Just Observes
  "observation" -> Just Observes  -- noema-core の observationKind と互換
  "tracks" -> Just Tracks
  -- 行為的関係
  "acts_for" -> Just ActsFor
  "agency" -> Just ActsFor  -- noema-core の agencyKind と互換
  -- 消極的関係
  "restricts" -> Just Restricts
  "restriction" -> Just Restricts  -- noema-core の restrictionKind と互換
  -- 不明
  _ -> Nothing
