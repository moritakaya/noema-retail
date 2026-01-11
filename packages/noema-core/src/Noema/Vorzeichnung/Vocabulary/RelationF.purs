-- | Noema Vocabulary: RelationF（関係性）
-- |
-- | Subject と Thing 間の関係を定義する。
-- |
-- | ## 圏論的位置づけ
-- |
-- | RelationF は Span 圏の操作を定義する Functor。
-- | 関係は Subject-Thing 間の射として表現される。
-- |
-- | ## Source of Truth
-- |
-- | 所有権等の Master Data は Thing を包摂する Subject が保持。
-- | Container の Contents は View（キャッシュ）。
-- |
-- | ## ドメイン非依存設計
-- |
-- | RelationKind は抽象的な Json newtype。
-- | 具体的な関係種別（Owns, Reserves 等）は各ドメイン層で定義する。
-- | noema-retail では RetailRelationKind として具体化。
module Noema.Vorzeichnung.Vocabulary.RelationF
  ( -- * RelationKind（抽象）
    RelationKind(..)
  , mkRelationKind
  , getRelationKindType
  , getRelationKindCategory
    -- * 定義済み定数（ドメイン非依存）
  , containmentKind
  , observationKind
  , agencyKind
  , restrictionKind
    -- * ChangeType（抽象）
  , ChangeType(..)
  , mkChangeType
  , getChangeType
    -- * SecurityType（抽象）
  , SecurityType(..)
  , mkSecurityType
  , getSecurityType
    -- * その他の型
  , AgencyScope(..)
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
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Argonaut.Core (Json, jsonNull, stringify, fromObject, fromString, toObject, toString)
import Data.Tuple.Nested ((/\))
import Foreign.Object as Object
import Noema.Topos.Situs
  ( ThingId, SubjectId, RelationId, SedimentId
  , Timestamp, ContractId, Quantity
  )

-- | 関係の種別（ドメイン非依存）
-- |
-- | Json として格納され、各ドメインで解釈される。
-- | noema-retail では RetailRelationKind への変換を提供。
-- |
-- | ## 構造
-- |
-- | ```json
-- | { "type": "containment", "category": "spatial", "subtype": null }
-- | { "type": "owns", "category": "rights", "subtype": null }
-- | ```
-- |
-- | ## カテゴリ
-- |
-- | - spatial: 空間的関係（包摂）
-- | - rights: 権利関係
-- | - temporal: 時間的関係（引当）
-- | - transitive: 過渡的関係（移動）
-- | - structural: 構造的関係（構成）
-- | - cognitive: 認識的関係（観測）
-- | - performative: 行為的関係（代理）
-- | - negative: 消極的関係（制限）
newtype RelationKind = RelationKind Json

derive instance eqRelationKind :: Eq RelationKind
derive instance newtypeRelationKind :: Newtype RelationKind _

instance showRelationKind :: Show RelationKind where
  show (RelationKind json) = "(RelationKind " <> stringify json <> ")"

-- | RelationKind を作成
-- |
-- | kindType と category を指定して作成する。
-- | 各ドメインはこの関数を使って具体的な関係種別を構築する。
mkRelationKind :: String -> String -> Maybe String -> RelationKind
mkRelationKind kindType category subtype =
  RelationKind $ fromObject $ Object.fromFoldable
    [ "type" /\ fromString kindType
    , "category" /\ fromString category
    , "subtype" /\ case subtype of
        Just s -> fromString s
        Nothing -> jsonNull
    ]

-- | RelationKind から type を取得
getRelationKindType :: RelationKind -> String
getRelationKindType (RelationKind json) =
  case toObject json of
    Just obj -> case Object.lookup "type" obj >>= toString of
      Just t -> t
      Nothing -> "unknown"
    Nothing -> "unknown"

-- | RelationKind から category を取得
getRelationKindCategory :: RelationKind -> String
getRelationKindCategory (RelationKind json) =
  case toObject json of
    Just obj -> case Object.lookup "category" obj >>= toString of
      Just c -> c
      Nothing -> "unknown"
    Nothing -> "unknown"

-- ============================================================
-- 定義済み定数（ドメイン非依存の基本概念）
-- ============================================================

-- | 包含関係（空間的）
containmentKind :: RelationKind
containmentKind = mkRelationKind "containment" "spatial" Nothing

-- | 観測関係（認識的）
observationKind :: RelationKind
observationKind = mkRelationKind "observation" "cognitive" Nothing

-- | 代理関係（行為的）
agencyKind :: RelationKind
agencyKind = mkRelationKind "agency" "performative" Nothing

-- | 制限関係（消極的）
restrictionKind :: RelationKind
restrictionKind = mkRelationKind "restriction" "negative" Nothing

-- | 担保権の種類（ドメイン非依存）
-- |
-- | 文字列として格納され、各ドメインで解釈される。
-- | noema-retail では RetailSecurityType として具体化。
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | let pledge = mkSecurityType "pledge"
-- | getSecurityType pledge == "pledge"
-- | ```
newtype SecurityType = SecurityType String

derive instance eqSecurityType :: Eq SecurityType
derive instance newtypeSecurityType :: Newtype SecurityType _

instance showSecurityType :: Show SecurityType where
  show (SecurityType s) = "(SecurityType " <> show s <> ")"

-- | SecurityType を作成
mkSecurityType :: String -> SecurityType
mkSecurityType = SecurityType

-- | SecurityType から型を取得
getSecurityType :: SecurityType -> String
getSecurityType (SecurityType s) = s

-- | 代理の範囲
data AgencyScope
  = GeneralAgency     -- 包括代理
  | SpecificAgency    -- 特定代理
  | LimitedAgency     -- 制限代理

derive instance eqAgencyScope :: Eq AgencyScope

-- | 通知すべき変化の種類（ドメイン非依存）
-- |
-- | 文字列として格納され、各ドメインで解釈される。
-- | noema-retail では RetailChangeType として具体化。
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | let priceChange = mkChangeType "price_changed"
-- | getChangeType priceChange == "price_changed"
-- | ```
newtype ChangeType = ChangeType String

derive instance eqChangeType :: Eq ChangeType
derive instance newtypeChangeType :: Newtype ChangeType _

instance showChangeType :: Show ChangeType where
  show (ChangeType s) = "(ChangeType " <> show s <> ")"

-- | ChangeType を作成
mkChangeType :: String -> ChangeType
mkChangeType = ChangeType

-- | ChangeType から型を取得
getChangeType :: ChangeType -> String
getChangeType (ChangeType s) = s

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
