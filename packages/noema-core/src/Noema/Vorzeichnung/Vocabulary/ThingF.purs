-- | Noema Vocabulary: ThingF（意志を持たない物）
-- |
-- | Thing は意志を持たない物。Subject に包摂され、
-- | Subject^op → Set として観測される。
-- |
-- | ## 圏論的位置づけ
-- |
-- | ThingF は Fiber 圏の操作を定義する Functor。
-- | Thing の同一性は包摂する Subject の id で決まる。
-- |
-- | ## 時間構造（Husserl）
-- |
-- | - Retention（把持）: 過去の Snapshot
-- | - Primal（原印象）: 現在の状態
-- | - Protention（予持）: 未来の Pending Intent
module Noema.Vorzeichnung.Vocabulary.ThingF
  ( PropertyKey(..)
  , PropertyValue
  , TimeRange
  , ChangeReason(..)
  , LocusChange
  , PendingIntent
  , ProtentionId(..)
  , ThingSnapshot
  , ThingState
  , Sediment
  , ThingF(..)
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Map (Map)
import Data.Argonaut.Core (Json)
import Noema.Topos.Situs (ThingId, SubjectId, SedimentId, Timestamp, ContractId)

-- | Property のキー
newtype PropertyKey = PropertyKey String

derive instance eqPropertyKey :: Eq PropertyKey
derive instance ordPropertyKey :: Ord PropertyKey
derive newtype instance showPropertyKey :: Show PropertyKey

-- | Property の値（任意の JSON）
type PropertyValue = Json

-- | 時間範囲
type TimeRange =
  { from :: Timestamp
  , to :: Timestamp
  }

-- | 位置変更の理由
data ChangeReason
  = Sale ContractId       -- 販売
  | Purchase ContractId   -- 購入
  | Transfer              -- 移動（内部）
  | Return ContractId     -- 返品
  | Adjustment String     -- 調整（棚卸等）

derive instance eqChangeReason :: Eq ChangeReason

instance showChangeReason :: Show ChangeReason where
  show (Sale cid) = "(Sale " <> show cid <> ")"
  show (Purchase cid) = "(Purchase " <> show cid <> ")"
  show Transfer = "Transfer"
  show (Return cid) = "(Return " <> show cid <> ")"
  show (Adjustment reason) = "(Adjustment " <> reason <> ")"

-- | 位置変更の記録
type LocusChange =
  { from :: SubjectId
  , to :: SubjectId
  , reason :: ChangeReason
  , contractRef :: Maybe ContractId
  }

-- | Pending Intent（予持）
-- | 未来に実行される予定の Intent
type PendingIntent =
  { scheduledAt :: Timestamp
  , intentBody :: Json
  , condition :: Maybe String  -- 条件（オプション）
  }

-- | Protention の識別子
newtype ProtentionId = ProtentionId String

derive instance eqProtentionId :: Eq ProtentionId
derive instance ordProtentionId :: Ord ProtentionId
derive newtype instance showProtentionId :: Show ProtentionId

-- | Thing の Snapshot（過去の把持）
-- | ある時点での Thing の完全な状態
type ThingSnapshot =
  { thingId :: ThingId
  , timestamp :: Timestamp
  , properties :: Map PropertyKey PropertyValue
  , locus :: SubjectId
  , sedimentId :: SedimentId
  }

-- | Thing の現在状態（原印象）
type ThingState =
  { thingId :: ThingId
  , properties :: Map PropertyKey PropertyValue
  , locus :: SubjectId
  , lastModified :: Timestamp
  , protentions :: Array ProtentionId
  }

-- | Sediment レコード
-- | 状態変更の不変記録（INSERT のみ、UPDATE 禁止）
type Sediment =
  { sequenceId :: Int
  , intentType :: String
  , payload :: Json
  , createdAt :: Timestamp
  }

-- | ThingF: もの・ことへの操作
-- |
-- | 時間構造（Husserl）に基づく三層：
-- | - Retention: 過去の把持（Snapshot）
-- | - Primal: 現在（最新の Sediment 積分値）
-- | - Protention: 未来の予持（Alarm と連動）
data ThingF i o
  -- === 属性 (Property) ===
  = GetProperty ThingId PropertyKey (i -> Unit) (PropertyValue -> o)
  | SetProperty ThingId PropertyKey (i -> PropertyValue) (SedimentId -> o)

  -- === 位置 (Locus) ===
  | GetLocus ThingId (i -> Unit) (SubjectId -> o)
  | RecordLocusChange ThingId (i -> LocusChange) (SedimentId -> o)

  -- === 時間 (Temporality) ===

  -- Retention: 過去の把持
  | GetRetention ThingId Timestamp (i -> Unit) (ThingSnapshot -> o)
  | GetRetentionRange ThingId TimeRange (i -> Unit) (Array Sediment -> o)

  -- Primal: 現在
  | GetPrimal ThingId (i -> Unit) (ThingState -> o)

  -- Protention: 未来の予持
  | RegisterProtention ThingId (i -> PendingIntent) (ProtentionId -> o)
  | GetProtentions ThingId (i -> Unit) (Array PendingIntent -> o)
  | RealizeProtention ProtentionId (i -> Unit) (SedimentId -> o)
  | CancelProtention ProtentionId (i -> Unit) (Unit -> o)

-- | Functor instance
instance functorThingF :: Functor (ThingF i) where
  map f = case _ of
    GetProperty tid key toUnit k -> GetProperty tid key toUnit (f <<< k)
    SetProperty tid key toVal k -> SetProperty tid key toVal (f <<< k)
    GetLocus tid toUnit k -> GetLocus tid toUnit (f <<< k)
    RecordLocusChange tid toChange k -> RecordLocusChange tid toChange (f <<< k)
    GetRetention tid ts toUnit k -> GetRetention tid ts toUnit (f <<< k)
    GetRetentionRange tid range toUnit k -> GetRetentionRange tid range toUnit (f <<< k)
    GetPrimal tid toUnit k -> GetPrimal tid toUnit (f <<< k)
    RegisterProtention tid toPending k -> RegisterProtention tid toPending (f <<< k)
    GetProtentions tid toUnit k -> GetProtentions tid toUnit (f <<< k)
    RealizeProtention pid toUnit k -> RealizeProtention pid toUnit (f <<< k)
    CancelProtention pid toUnit k -> CancelProtention pid toUnit (f <<< k)
