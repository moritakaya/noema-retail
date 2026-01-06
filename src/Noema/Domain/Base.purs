-- | Noema Retail: 基本型
-- |
-- | すべてのドメインモジュールで共有される基本型を定義する。
-- |
-- | 圏論的構造：
-- | - 各 ID 型は識別子の圏における対象
-- | - Timestamp は時間の全順序集合
module Noema.Domain.Base
  ( ThingId(..)
  , SubjectId(..)
  , ContractId(..)
  , Timestamp(..)
  , LocationId(..)
  , mkThingId
  , mkSubjectId
  , mkContractId
  , mkTimestamp
  , mkLocationId
  , timestampToNumber
  , currentTimestamp
  ) where

import Prelude

import Data.Newtype (class Newtype, unwrap)
import Effect (Effect)
import Data.Generic.Rep (class Generic)

--------------------------------------------------------------------------------
-- Thing（物）の識別子
--------------------------------------------------------------------------------

-- | 商品・物品の識別子
-- |
-- | Thing 圏の対象を表す。
newtype ThingId = ThingId String

derive instance Newtype ThingId _
derive instance Eq ThingId
derive instance Ord ThingId
derive instance Generic ThingId _
derive newtype instance Show ThingId

mkThingId :: String -> ThingId
mkThingId = ThingId

--------------------------------------------------------------------------------
-- Subject（主体）の識別子
--------------------------------------------------------------------------------

-- | 契約主体（買手・売手）の識別子
-- |
-- | Subject 圏の対象を表す。
newtype SubjectId = SubjectId String

derive instance Newtype SubjectId _
derive instance Eq SubjectId
derive instance Ord SubjectId
derive instance Generic SubjectId _
derive newtype instance Show SubjectId

mkSubjectId :: String -> SubjectId
mkSubjectId = SubjectId

--------------------------------------------------------------------------------
-- Contract（契約）の識別子
--------------------------------------------------------------------------------

-- | 契約の識別子
-- |
-- | 契約は Subject 間の関係を定義する。
newtype ContractId = ContractId String

derive instance Newtype ContractId _
derive instance Eq ContractId
derive instance Ord ContractId
derive instance Generic ContractId _
derive newtype instance Show ContractId

mkContractId :: String -> ContractId
mkContractId = ContractId

--------------------------------------------------------------------------------
-- Timestamp（時刻）
--------------------------------------------------------------------------------

-- | Unix ミリ秒タイムスタンプ
-- |
-- | Context 圏の時間軸を表す。
-- | 全順序関係が定義されており、イベントの順序付けに使用される。
newtype Timestamp = Timestamp Number

derive instance Newtype Timestamp _
derive instance Eq Timestamp
derive instance Ord Timestamp
derive instance Generic Timestamp _
derive newtype instance Show Timestamp

mkTimestamp :: Number -> Timestamp
mkTimestamp = Timestamp

timestampToNumber :: Timestamp -> Number
timestampToNumber = unwrap

-- | 現在時刻を取得
foreign import currentTimestamp :: Effect Timestamp

--------------------------------------------------------------------------------
-- Location（場所）の識別子
--------------------------------------------------------------------------------

-- | 在庫ロケーションの識別子
-- |
-- | 倉庫、店舗、仮想ロケーションを識別する。
newtype LocationId = LocationId String

derive instance Newtype LocationId _
derive instance Eq LocationId
derive instance Ord LocationId
derive instance Generic LocationId _
derive newtype instance Show LocationId

mkLocationId :: String -> LocationId
mkLocationId = LocationId
