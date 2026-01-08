-- | Noema Core: Locus（空間座標）
-- |
-- | DO の識別子と基本型を定義する。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Locus は Base 圏の対象を識別する。
-- | DO が眠って起きた時、Locus は同じだが World が変わりうる。
module Noema.Core.Locus
  ( LocusId(..)
  , SubjectId(..)
  , ThingId(..)
  , ContractId(..)
  , RelationId(..)
  , SedimentId(..)
  , Timestamp(..)
  , Quantity(..)
  ) where

import Prelude

-- | DO の識別子（空間座標）
newtype LocusId = LocusId String

derive instance eqLocusId :: Eq LocusId
derive instance ordLocusId :: Ord LocusId
derive newtype instance showLocusId :: Show LocusId

-- | Subject の識別子（意志を持つ主体）
-- | Subject は DO として実装される
newtype SubjectId = SubjectId LocusId

derive instance eqSubjectId :: Eq SubjectId
derive instance ordSubjectId :: Ord SubjectId

instance showSubjectId :: Show SubjectId where
  show (SubjectId (LocusId s)) = "(SubjectId " <> s <> ")"

-- | Thing の識別子（意志を持たない物）
-- | Thing は DO ではない。Guardian Subject に包摂される
newtype ThingId = ThingId String

derive instance eqThingId :: Eq ThingId
derive instance ordThingId :: Ord ThingId
derive newtype instance showThingId :: Show ThingId

-- | Contract の識別子
-- | Contract は DO として実装される
newtype ContractId = ContractId LocusId

derive instance eqContractId :: Eq ContractId
derive instance ordContractId :: Ord ContractId

instance showContractId :: Show ContractId where
  show (ContractId (LocusId s)) = "(ContractId " <> s <> ")"

-- | Relation の識別子
newtype RelationId = RelationId String

derive instance eqRelationId :: Eq RelationId
derive instance ordRelationId :: Ord RelationId
derive newtype instance showRelationId :: Show RelationId

-- | Sediment の識別子（Lamport Clock）
-- | 各 DO 内で単調増加する
newtype SedimentId = SedimentId Int

derive instance eqSedimentId :: Eq SedimentId
derive instance ordSedimentId :: Ord SedimentId
derive newtype instance showSedimentId :: Show SedimentId

-- | Timestamp（エポックミリ秒）
newtype Timestamp = Timestamp Number

derive instance eqTimestamp :: Eq Timestamp
derive instance ordTimestamp :: Ord Timestamp
derive newtype instance showTimestamp :: Show Timestamp

-- | Quantity（数量）
newtype Quantity = Quantity Int

derive instance eqQuantity :: Eq Quantity
derive instance ordQuantity :: Ord Quantity
derive newtype instance showQuantity :: Show Quantity
derive newtype instance semiringQuantity :: Semiring Quantity
