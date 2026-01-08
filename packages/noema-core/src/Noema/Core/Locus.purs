-- | Noema Core: Locus（空間座標）
-- |
-- | DO の識別子と基本型を定義する。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Locus は Base 圏の対象を識別する。
-- | DO が眠って起きた時、Locus は同じだが World が変わりうる。
-- |
-- | ## 存在論的構造
-- |
-- | - Subject: 意志を持つ主体（DO として実装）
-- | - Thing: 意志を持たない物（Subject に包摂）
-- | - Contract: 契約（DO として実装）
-- |
-- | 注: LocationId は廃止。Subject が Thing を包摂し、その位置を決定する。
module Noema.Core.Locus
  ( -- * Locus（空間座標）
    LocusId(..)
  , mkLocusId
    -- * Subject（意志を持つ主体）
  , SubjectId(..)
  , mkSubjectId
  , unwrapSubjectId
    -- * Thing（意志を持たない物）
  , ThingId(..)
  , mkThingId
  , unwrapThingId
    -- * Contract（契約）
  , ContractId(..)
  , mkContractId
  , unwrapContractId
    -- * Relation（関係）
  , RelationId(..)
  , mkRelationId
    -- * Sediment（沈殿記録）
  , SedimentId(..)
  , mkSedimentId
    -- * Timestamp（時刻）
  , Timestamp(..)
  , mkTimestamp
  , timestampToNumber
  , currentTimestamp
    -- * Quantity（数量）
  , Quantity(..)
  , mkQuantity
  , unwrapQuantity
    -- * QuantityDelta（数量変化）
  , QuantityDelta(..)
  , mkQuantityDelta
  , unwrapQuantityDelta
  ) where

import Prelude

import Data.Newtype (class Newtype, unwrap)
import Effect (Effect)

-- ============================================================
-- LocusId: DO の識別子（空間座標）
-- ============================================================

-- | DO の識別子（空間座標）
newtype LocusId = LocusId String

derive instance Newtype LocusId _
derive instance eqLocusId :: Eq LocusId
derive instance ordLocusId :: Ord LocusId
derive newtype instance showLocusId :: Show LocusId

mkLocusId :: String -> LocusId
mkLocusId = LocusId

-- ============================================================
-- SubjectId: 意志を持つ主体
-- ============================================================

-- | Subject の識別子（意志を持つ主体）
-- |
-- | Subject は DO として実装される。
-- | Subject は Thing を包摂し、その位置を決定する。
-- |
-- | 注: 旧設計の LocationId は SubjectId に統合された。
newtype SubjectId = SubjectId LocusId

derive instance Newtype SubjectId _
derive instance eqSubjectId :: Eq SubjectId
derive instance ordSubjectId :: Ord SubjectId

instance showSubjectId :: Show SubjectId where
  show (SubjectId (LocusId s)) = "(SubjectId " <> s <> ")"

mkSubjectId :: String -> SubjectId
mkSubjectId s = SubjectId (LocusId s)

unwrapSubjectId :: SubjectId -> String
unwrapSubjectId (SubjectId (LocusId s)) = s

-- ============================================================
-- ThingId: 意志を持たない物
-- ============================================================

-- | Thing の識別子（意志を持たない物）
-- |
-- | Thing は DO ではない。Subject に包摂される。
-- | Thing の同一性は包摂する Subject の id で決まる。
newtype ThingId = ThingId String

derive instance Newtype ThingId _
derive instance eqThingId :: Eq ThingId
derive instance ordThingId :: Ord ThingId
derive newtype instance showThingId :: Show ThingId

mkThingId :: String -> ThingId
mkThingId = ThingId

unwrapThingId :: ThingId -> String
unwrapThingId = unwrap

-- ============================================================
-- ContractId: 契約
-- ============================================================

-- | Contract の識別子
-- |
-- | Contract は DO として実装される。
newtype ContractId = ContractId LocusId

derive instance Newtype ContractId _
derive instance eqContractId :: Eq ContractId
derive instance ordContractId :: Ord ContractId

instance showContractId :: Show ContractId where
  show (ContractId (LocusId s)) = "(ContractId " <> s <> ")"

mkContractId :: String -> ContractId
mkContractId s = ContractId (LocusId s)

unwrapContractId :: ContractId -> String
unwrapContractId (ContractId (LocusId s)) = s

-- ============================================================
-- RelationId: 関係
-- ============================================================

-- | Relation の識別子
newtype RelationId = RelationId String

derive instance Newtype RelationId _
derive instance eqRelationId :: Eq RelationId
derive instance ordRelationId :: Ord RelationId
derive newtype instance showRelationId :: Show RelationId

mkRelationId :: String -> RelationId
mkRelationId = RelationId

-- ============================================================
-- SedimentId: 沈殿記録
-- ============================================================

-- | Sediment の識別子（Lamport Clock）
-- |
-- | 各 DO 内で単調増加する。
-- | Sediment は状態変更の不変記録。
newtype SedimentId = SedimentId Int

derive instance Newtype SedimentId _
derive instance eqSedimentId :: Eq SedimentId
derive instance ordSedimentId :: Ord SedimentId
derive newtype instance showSedimentId :: Show SedimentId

mkSedimentId :: Int -> SedimentId
mkSedimentId = SedimentId

-- ============================================================
-- Timestamp: 時刻
-- ============================================================

-- | Timestamp（エポックミリ秒）
-- |
-- | 全順序関係が定義されており、イベントの順序付けに使用される。
newtype Timestamp = Timestamp Number

derive instance Newtype Timestamp _
derive instance eqTimestamp :: Eq Timestamp
derive instance ordTimestamp :: Ord Timestamp
derive newtype instance showTimestamp :: Show Timestamp

mkTimestamp :: Number -> Timestamp
mkTimestamp = Timestamp

timestampToNumber :: Timestamp -> Number
timestampToNumber = unwrap

-- | 現在時刻を取得
foreign import currentTimestamp :: Effect Timestamp

-- ============================================================
-- Quantity: 数量
-- ============================================================

-- | Quantity（数量、非負整数）
newtype Quantity = Quantity Int

derive instance Newtype Quantity _
derive instance eqQuantity :: Eq Quantity
derive instance ordQuantity :: Ord Quantity
derive newtype instance showQuantity :: Show Quantity
derive newtype instance semiringQuantity :: Semiring Quantity

mkQuantity :: Int -> Quantity
mkQuantity = Quantity

unwrapQuantity :: Quantity -> Int
unwrapQuantity = unwrap

-- ============================================================
-- QuantityDelta: 数量変化
-- ============================================================

-- | QuantityDelta（数量の変化、正負あり）
newtype QuantityDelta = QuantityDelta Int

derive instance Newtype QuantityDelta _
derive instance eqQuantityDelta :: Eq QuantityDelta
derive newtype instance showQuantityDelta :: Show QuantityDelta
derive newtype instance semiringQuantityDelta :: Semiring QuantityDelta
derive newtype instance ringQuantityDelta :: Ring QuantityDelta

mkQuantityDelta :: Int -> QuantityDelta
mkQuantityDelta = QuantityDelta

unwrapQuantityDelta :: QuantityDelta -> Int
unwrapQuantityDelta = unwrap
