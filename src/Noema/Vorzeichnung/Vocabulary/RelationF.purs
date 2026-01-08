-- | Noema Vocabulary: RelationF（関係性）
-- |
-- | Subject と Thing 間の関係を定義する。
-- | 所有権、占有権、担保権などの法的関係を含む。
-- |
-- | ## 圏論的位置づけ
-- |
-- | RelationF は Span 圏の操作を定義する Functor。
-- | 関係は Subject-Thing 間の射として表現される。
-- |
-- | ## Source of Truth
-- |
-- | 所有権等の Master Data は Thing Guardian が保持。
-- | Container の Contents は View（キャッシュ）。
module Noema.Vorzeichnung.Vocabulary.RelationF
  ( RelationKind(..)
  , SecurityType(..)
  , AgencyScope(..)
  , ChangeType(..)
  , ConditionType(..)
  , RelationMetadata(..)
  , Relation
  , RelationInit
  , OwnershipTransfer
  , ObserverContext
  , ThingView
  , IntentionView
  , RelationF(..)
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Argonaut.Core (Json)
import Noema.Core.Locus
  ( ThingId, SubjectId, RelationId, SedimentId
  , Timestamp, ContractId, Quantity
  )

-- | 関係の種別
data RelationKind
  -- 包摂関係（空間的）
  = Contains      -- Subject が Thing を物理的に含む
  | Guards        -- Subject が Thing の Guardian である

  -- 権利関係（法的）
  | Owns          -- 所有権
  | Possesses     -- 占有権
  | Claims        -- 請求権
  | Secures       -- 担保権
  | SharedBy      -- 共有

  -- 引当関係（時間的）
  | Reserves      -- 引当（一時的確保）
  | Commits       -- 確約（確定的確保）
  | Intends       -- 意図（購入意思の表明、引当なし）

  -- 移動関係（過渡的）
  | Transports    -- 輸送中
  | Consigns      -- 委託中

  -- 構成関係（構造的）
  | ComposedOf    -- 部品構成
  | BundledWith   -- セット構成
  | Substitutes   -- 代替関係

  -- 観測関係（認識的）
  | Observes      -- Channel からの観測
  | Tracks        -- 追跡

  -- 代理関係（行為的）
  | ActsFor       -- 代理

  -- 制限関係（消極的）
  | Restricts     -- 処分制限

derive instance eqRelationKind :: Eq RelationKind

instance showRelationKind :: Show RelationKind where
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

-- | 担保権の種類
data SecurityType
  = Pledge            -- 質権
  | Lien              -- 留置権
  | Mortgage          -- 抵当権
  | SecurityInterest  -- 譲渡担保
  | RetentionOfTitle  -- 所有権留保

derive instance eqSecurityType :: Eq SecurityType

-- | 代理の範囲
data AgencyScope
  = GeneralAgency     -- 包括代理
  | SpecificAgency    -- 特定代理
  | LimitedAgency     -- 制限代理

derive instance eqAgencyScope :: Eq AgencyScope

-- | 通知すべき変化の種類
data ChangeType
  = PriceChanged
  | AvailabilityChanged
  | PropertyChanged
  | Discontinued

derive instance eqChangeType :: Eq ChangeType

-- | 条件の種類
data ConditionType
  = PaymentComplete ContractId Number
  | TimeElapsed Timestamp
  | ObligationFulfilled String

derive instance eqConditionType :: Eq ConditionType

-- | 関係のメタデータ
data RelationMetadata
  = SharedByMeta { share :: Number }  -- Rational の代わりに Number
  | ActsForMeta { scope :: AgencyScope, disclosed :: Boolean }
  | SecuresMeta
      { securityType :: SecurityType
      , priority :: Int
      , amount :: Maybe Number
      , securedContract :: Maybe ContractId
      , ariseFrom :: Maybe ContractId
      }
  | ExpirationMeta { expiresAt :: Timestamp }
  | ConditionalMeta { condition :: ConditionType, pendingRelation :: RelationKind }
  | IntendsMeta { quantity :: Quantity, notifyOn :: Array ChangeType }

-- | 関係
type Relation =
  { id :: RelationId
  , kind :: RelationKind
  , from :: SubjectId
  , to :: ThingId
  , metadata :: Maybe RelationMetadata
  , validFrom :: Timestamp
  , validUntil :: Maybe Timestamp
  , contractRef :: Maybe ContractId
  , createdAt :: Timestamp
  }

-- | 関係の初期化
type RelationInit =
  { kind :: RelationKind
  , from :: SubjectId
  , to :: ThingId
  , metadata :: Maybe RelationMetadata
  , validUntil :: Maybe Timestamp
  , contractRef :: Maybe ContractId
  }

-- | 所有権移転の記録
type OwnershipTransfer =
  { thing :: ThingId
  , from :: SubjectId
  , to :: SubjectId
  , via :: Maybe SubjectId  -- 中間者（代理人など）
  , contractRef :: ContractId
  , timestamp :: Timestamp
  }

-- | 観測コンテキスト
type ObserverContext =
  { channelId :: String
  , permissions :: Array String
  }

-- | Thing の View（観測者から見た状態）
type ThingView =
  { thingId :: ThingId
  , visibleProperties :: Json
  , quantity :: Maybe Quantity
  }

-- | 意図の View
type IntentionView =
  { thingId :: ThingId
  , quantity :: Quantity
  , intendedAt :: Timestamp
  , expiresAt :: Maybe Timestamp
  }

-- | RelationF: 関係性の操作
data RelationF i o
  -- 関係の照会
  = GetRelation RelationId (i -> Unit) (Maybe Relation -> o)
  | GetRelationsFrom SubjectId RelationKind (i -> Unit) (Array Relation -> o)
  | GetRelationsTo ThingId RelationKind (i -> Unit) (Array Relation -> o)

  -- 関係の操作
  | AddRelation (i -> RelationInit) (RelationId -> o)
  | RemoveRelation RelationId (i -> Unit) (SedimentId -> o)
  | UpdateRelationMetadata RelationId (i -> RelationMetadata) (SedimentId -> o)

  -- 所有権移転（経路を記録）
  | RecordOwnershipTransfer (i -> OwnershipTransfer) (SedimentId -> o)

  -- 集約照会
  | GetContents SubjectId (i -> Unit) (Array ThingId -> o)
  | GetObservedThings SubjectId ObserverContext (i -> Unit) (Array ThingView -> o)
  | GetIntendedThings SubjectId (i -> Unit) (Array IntentionView -> o)

-- | Functor instance
instance functorRelationF :: Functor (RelationF i) where
  map f = case _ of
    GetRelation rid toUnit k -> GetRelation rid toUnit (f <<< k)
    GetRelationsFrom sid kind toUnit k -> GetRelationsFrom sid kind toUnit (f <<< k)
    GetRelationsTo tid kind toUnit k -> GetRelationsTo tid kind toUnit (f <<< k)
    AddRelation toInit k -> AddRelation toInit (f <<< k)
    RemoveRelation rid toUnit k -> RemoveRelation rid toUnit (f <<< k)
    UpdateRelationMetadata rid toMeta k -> UpdateRelationMetadata rid toMeta (f <<< k)
    RecordOwnershipTransfer toTransfer k -> RecordOwnershipTransfer toTransfer (f <<< k)
    GetContents sid toUnit k -> GetContents sid toUnit (f <<< k)
    GetObservedThings sid ctx toUnit k -> GetObservedThings sid ctx toUnit (f <<< k)
    GetIntendedThings sid toUnit k -> GetIntendedThings sid toUnit (f <<< k)
