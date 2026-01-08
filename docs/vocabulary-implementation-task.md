# Noema Vocabulary 再設計: 実装タスク

## 概要

Noema DSL の Vocabulary を再設計した。イミュータブルデータモデルと AVDC（Augmented Virtual Double Category）に基づく設計。

**参照すべきリポジトリ**: https://github.com/moritakaya/noema-retail

## 設計原理

### 1. 存在論的三層構造

```
┌─────────────────────────────────────────────────────────────────────┐
│  Nomos（大域意志）                                                   │
│  法律、商習慣、ビジネスルール                                        │
│  Sediment の解釈を規定する「法」                                     │
└─────────────────────────────────────────────────────────────────────┘
                         ↓ 規定
┌─────────────────────────────────────────────────────────────────────┐
│  Subject（意志を持つ主体）        Thing（意志を持たない物）          │
│  DO として実装                    Subject に包摂される              │
│  能動的に Sediment を沈殿         Subject^op → Set として観測される  │
└─────────────────────────────────────────────────────────────────────┘
```

### 2. グロタンディーク構成

```
Locus  = 空間座標（DO の ID）
World  = 法座標（Nomos のバージョン + 文脈）

Base 圏: DO のネットワーク（水平射 = RPC）
Fiber 圏: 各 DO 内の状態空間（垂直射 = Sediment）

DO が眠って起きた時:
  - Locus は同じ
  - World が変わりうる（コードのデプロイ）
```

### 3. Thing = Subject の包摂

```
Thing 自体は DO ではない。
Subject が Thing を「包摂」する。
Thing の同一性 = 包摂する Subject の id
Thing の状態 = Subject の Fiber 内 Sediment の積分値
```

## Vocabulary 構成

```purescript
type NoemaF = Coproduct4 SubjectF ThingF RelationF ContractF
```

| 語彙 | 圏論的位置 | 役割 |
|------|-----------|------|
| SubjectF | Base 圏の操作 | 意志を持つ主体の生成・照会・通信 |
| ThingF | Fiber 圏の操作 | もの・ことの属性・位置・時間 |
| RelationF | Span 圏の操作 | Subject-Thing 間の関係（View） |
| ContractF | 規定の圏の操作 | 権利・義務、契約間関係 |

---

## 実装タスク

### タスク1: 基本型の定義

**ファイル**: `src/Noema/Core/Locus.purs`

```purescript
module Noema.Core.Locus where

import Prelude
import Data.Maybe (Maybe)

-- | DO の識別子（空間座標）
newtype LocusId = LocusId String

derive instance eqLocusId :: Eq LocusId
derive instance ordLocusId :: Ord LocusId
derive newtype instance showLocusId :: Show LocusId

-- | Subject, Thing, Contract の識別子
newtype SubjectId = SubjectId LocusId
newtype ThingId = ThingId String  -- Thing は DO ではない
newtype ContractId = ContractId LocusId
newtype RelationId = RelationId String
newtype SedimentId = SedimentId Int  -- Lamport Clock

-- | Timestamp
newtype Timestamp = Timestamp Number

-- | Quantity
newtype Quantity = Quantity Int
```

**ファイル**: `src/Noema/Core/World.purs`

```purescript
module Noema.Core.World where

import Prelude
import Data.Maybe (Maybe)
import Noema.Core.Locus (Timestamp)

-- | Nomos のバージョン
newtype NomosVersion = NomosVersion String

-- | World = Nomos の適用文脈（法座標）
type World = 
  { nomosVersion :: NomosVersion
  , region :: Maybe String
  , timestamp :: Timestamp
  }

-- | Intent の文脈
type IntentContext =
  { origin :: World
  , target :: World
  }
```

---

### タスク2: SubjectF の実装

**ファイル**: `src/Noema/Vorzeichnung/Vocabulary/SubjectF.purs`

```purescript
module Noema.Vorzeichnung.Vocabulary.SubjectF where

import Prelude
import Data.Maybe (Maybe)
import Data.Argonaut.Core (Json)
import Noema.Core.Locus (SubjectId, SedimentId, Timestamp)
import Noema.Core.World (World, IntentContext)

-- | Subject の種別
data SubjectKind
  = ContractParty    -- 契約主体
  | ThingHolder      -- Thing を包摂する Subject
  | SystemAgent      -- システムエージェント

derive instance eqSubjectKind :: Eq SubjectKind

-- | Subject の状態
type SubjectState =
  { id :: SubjectId
  , kind :: SubjectKind
  , world :: World
  , lastActivity :: Timestamp
  }

-- | Subject 初期化
type SubjectInit =
  { kind :: SubjectKind
  , world :: World
  }

-- | Subject 更新
type SubjectPatch =
  { world :: Maybe World
  }

-- | Intent の封筒
type IntentEnvelope =
  { body :: Json
  , context :: IntentContext
  , seal :: String  -- 正当性の証明
  }

-- | 受領証
type Receipt =
  { id :: String
  , timestamp :: Timestamp
  , accepted :: Boolean
  }

-- | SubjectF: 意志を持つ主体への操作
data SubjectF i o
  -- Subject の生成・照会
  = CreateSubject (i -> SubjectInit) (SubjectId -> o)
  | GetSubject SubjectId (i -> Unit) (SubjectState -> o)
  | GetSubjectsByKind SubjectKind (i -> Unit) (Array SubjectState -> o)
  
  -- Subject の状態変更
  | UpdateSubject SubjectId (i -> SubjectPatch) (SedimentId -> o)
  
  -- 水平射（Subject 間通信）
  | SendIntent SubjectId (i -> IntentEnvelope) (Receipt -> o)
  | ConfirmReceipt String (i -> Unit) (Unit -> o)

derive instance functorSubjectF :: Functor (SubjectF i)
```

---

### タスク3: ThingF の実装

**ファイル**: `src/Noema/Vorzeichnung/Vocabulary/ThingF.purs`

```purescript
module Noema.Vorzeichnung.Vocabulary.ThingF where

import Prelude
import Data.Maybe (Maybe)
import Data.Map (Map)
import Data.Argonaut.Core (Json)
import Noema.Core.Locus (ThingId, SubjectId, SedimentId, Timestamp, ContractId)

-- | Property のキーと値
newtype PropertyKey = PropertyKey String
type PropertyValue = Json

-- | 時間範囲
type TimeRange =
  { from :: Timestamp
  , to :: Timestamp
  }

-- | 位置変更の理由
data ChangeReason
  = Sale ContractId
  | Purchase ContractId
  | Transfer
  | Return ContractId
  | Adjustment String

-- | 位置変更の記録
type LocusChange =
  { from :: SubjectId
  , to :: SubjectId
  , reason :: ChangeReason
  , contractRef :: Maybe ContractId
  }

-- | Pending Intent（予持）
type PendingIntent =
  { scheduledAt :: Timestamp
  , intentBody :: Json
  , condition :: Maybe String
  }

newtype ProtentionId = ProtentionId String

-- | Thing の Snapshot（過去の把持）
type ThingSnapshot =
  { thingId :: ThingId
  , timestamp :: Timestamp
  , properties :: Map PropertyKey PropertyValue
  , locus :: SubjectId
  , sedimentId :: SedimentId
  }

-- | Thing の現在状態
type ThingState =
  { thingId :: ThingId
  , properties :: Map PropertyKey PropertyValue
  , locus :: SubjectId
  , lastModified :: Timestamp
  , protentions :: Array ProtentionId
  }

-- | Sediment レコード
type Sediment =
  { sequenceId :: Int
  , intentType :: String
  , payload :: Json
  , createdAt :: Timestamp
  }

-- | ThingF: もの・ことへの操作
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

derive instance functorThingF :: Functor (ThingF i)
```

---

### タスク4: RelationF の実装

**ファイル**: `src/Noema/Vorzeichnung/Vocabulary/RelationF.purs`

```purescript
module Noema.Vorzeichnung.Vocabulary.RelationF where

import Prelude
import Data.Maybe (Maybe)
import Data.Argonaut.Core (Json)
import Data.Rational (Rational)
import Noema.Core.Locus 
  ( ThingId, SubjectId, RelationId, SedimentId
  , Timestamp, ContractId, Quantity
  )

-- | 関係の種別
data RelationKind
  -- 包摂関係（空間的）
  = Contains      -- Subject が Thing を物理的に含む
  | Guards        -- Subject が Thing を包摂する
  
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

-- | 担保権の種類
data SecurityType
  = Pledge            -- 質権
  | Lien              -- 留置権
  | Mortgage          -- 抵当権
  | SecurityInterest  -- 譲渡担保
  | RetentionOfTitle  -- 所有権留保

-- | 代理の範囲
data AgencyScope
  = GeneralAgency     -- 包括代理
  | SpecificAgency    -- 特定代理
  | LimitedAgency     -- 制限代理

-- | 通知すべき変化の種類
data ChangeType
  = PriceChanged
  | AvailabilityChanged
  | PropertyChanged
  | Discontinued

-- | 条件の種類
data ConditionType
  = PaymentComplete ContractId Number
  | TimeElapsed Timestamp
  | ObligationFulfilled String

-- | 関係のメタデータ
data RelationMetadata
  = SharedByMeta { share :: Rational }
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
  , via :: Maybe SubjectId
  , contractRef :: ContractId
  , timestamp :: Timestamp
  }

-- | 観測コンテキスト
type ObserverContext =
  { channelId :: String
  , permissions :: Array String
  }

-- | Thing の View
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

derive instance functorRelationF :: Functor (RelationF i)
```

---

### タスク5: ContractF の実装

**ファイル**: `src/Noema/Vorzeichnung/Vocabulary/ContractF.purs`

```purescript
module Noema.Vorzeichnung.Vocabulary.ContractF where

import Prelude
import Data.Maybe (Maybe)
import Data.Argonaut.Core (Json)
import Noema.Core.Locus 
  ( ThingId, SubjectId, ContractId, SedimentId, Timestamp )
import Noema.Core.World (NomosReference)

-- | 契約の状態
data ContractStatus
  = Draft
  | Proposed
  | Accepted
  | InProgress
  | Fulfilled
  | Cancelled
  | Disputed

derive instance eqContractStatus :: Eq ContractStatus

-- | 義務の種類
data ObligationKind
  = Transfer      -- Thing の移転義務
  | Payment       -- 支払義務
  | Perform       -- 役務提供義務
  | Refrain       -- 不作為義務

-- | 義務の状態
data ObligationStatus
  = Pending
  | Fulfilled_
  | Breached
  | Waived

-- | 義務
type Obligation =
  { id :: String
  , kind :: ObligationKind
  , debtor :: SubjectId
  , creditor :: SubjectId
  , thingRef :: Maybe ThingId
  , amount :: Maybe Number
  , dueDate :: Maybe Timestamp
  , status :: ObligationStatus
  }

-- | 義務の定義
type ObligationDef =
  { kind :: ObligationKind
  , debtor :: SubjectId
  , creditor :: SubjectId
  , thingRef :: Maybe ThingId
  , amount :: Maybe Number
  , dueDate :: Maybe Timestamp
  }

-- | 履行の証明
type FulfillmentProof =
  { obligationId :: String
  , evidence :: Json
  , timestamp :: Timestamp
  }

-- | 契約当事者
type ContractParties =
  { partyA :: SubjectId
  , partyB :: SubjectId
  }

-- | 契約条項
type Term = Json

-- | 契約提案
type ContractProposal =
  { parties :: ContractParties
  , terms :: Array Term
  , thingRefs :: Array ThingId
  , nomosRef :: NomosReference
  }

-- | 契約の状態
type ContractState =
  { id :: ContractId
  , parties :: ContractParties
  , terms :: Array Term
  , thingRefs :: Array ThingId
  , status :: ContractStatus
  , obligations :: Array Obligation
  , createdAt :: Timestamp
  , updatedAt :: Timestamp
  }

-- | 拒否理由
type RejectReason = String

-- | 取消理由  
type CancelReason = String

-- | Contract 間の関係種別
data ContractRelationKind
  = Prerequisite    -- 前提
  | Subordinate     -- 従属
  | Consideration   -- 対価
  | Security        -- 担保
  | Amendment       -- 変更
  | Termination     -- 解除

-- | Contract 間の関係
type ContractRelation =
  { from :: ContractId
  , to :: ContractId
  , kind :: ContractRelationKind
  , description :: Maybe String
  }

-- | 契約グラフ
type ContractGraph =
  { contracts :: Array ContractState
  , relations :: Array ContractRelation
  }

-- | ContractF: 契約の操作
data ContractF i o
  -- 契約のライフサイクル
  = ProposeContract (i -> ContractProposal) (ContractId -> o)
  | AcceptContract ContractId (i -> Unit) (SedimentId -> o)
  | RejectContract ContractId (i -> RejectReason) (SedimentId -> o)
  | CancelContract ContractId (i -> CancelReason) (SedimentId -> o)
  
  -- 契約の照会
  | GetContract ContractId (i -> Unit) (ContractState -> o)
  | GetContractsByParty SubjectId (i -> Unit) (Array ContractState -> o)
  
  -- 義務の操作
  | AddObligation ContractId (i -> ObligationDef) (String -> o)
  | FulfillObligation String (i -> FulfillmentProof) (SedimentId -> o)
  | GetObligations ContractId (i -> Unit) (Array Obligation -> o)
  | GetPendingObligations SubjectId (i -> Unit) (Array Obligation -> o)
  
  -- Contract 間の関係
  | LinkContracts (i -> ContractRelation) (SedimentId -> o)
  | GetLinkedContracts ContractId ContractRelationKind (i -> Unit) (Array ContractId -> o)
  | GetContractChain ContractId (i -> Unit) (ContractGraph -> o)

derive instance functorContractF :: Functor (ContractF i)
```

---

### タスク6: 統合語彙

**ファイル**: `src/Noema/Vorzeichnung/Vocabulary/NoemaF.purs`

```purescript
module Noema.Vorzeichnung.Vocabulary.NoemaF where

import Prelude
import Data.Functor.Coproduct.Nested (Coproduct4)
import Noema.Vorzeichnung.Vocabulary.SubjectF (SubjectF)
import Noema.Vorzeichnung.Vocabulary.ThingF (ThingF)
import Noema.Vorzeichnung.Vocabulary.RelationF (RelationF)
import Noema.Vorzeichnung.Vocabulary.ContractF (ContractF)

-- | Noema 統合語彙
type NoemaF = Coproduct4 SubjectF ThingF RelationF ContractF
```

---

### タスク7: スマートコンストラクタ

**ファイル**: `src/Noema/Vorzeichnung/Vocabulary/Constructors.purs`

各語彙の操作を Intent として持ち上げるスマートコンストラクタを実装。

```purescript
module Noema.Vorzeichnung.Vocabulary.Constructors where

import Prelude
import Noema.Vorzeichnung.Intent (Intent', liftEffect)
import Noema.Vorzeichnung.Vocabulary.NoemaF (NoemaF)
import Noema.Vorzeichnung.Vocabulary.SubjectF as S
import Noema.Vorzeichnung.Vocabulary.ThingF as T
import Noema.Vorzeichnung.Vocabulary.RelationF as R
import Noema.Vorzeichnung.Vocabulary.ContractF as C
-- ... Coproduct injection helpers

-- Subject
createSubject :: Intent' NoemaF S.SubjectInit S.SubjectId
createSubject = liftSubject (S.CreateSubject identity identity)

-- Thing
getThingState :: T.ThingId -> Intent' NoemaF Unit T.ThingState
getThingState tid = liftThing (T.GetPrimal tid identity identity)

-- Relation
addRelation :: Intent' NoemaF R.RelationInit R.RelationId
addRelation = liftRelation (R.AddRelation identity identity)

-- Contract
proposeContract :: Intent' NoemaF C.ContractProposal C.ContractId
proposeContract = liftContract (C.ProposeContract identity identity)

-- ... 他のコンストラクタ
```

---

## ディレクトリ構造

```
src/Noema/
├── Core/
│   ├── Locus.purs          # 空間座標、識別子
│   └── World.purs          # 法座標、Nomos
│
├── Vorzeichnung/
│   ├── Intent.purs         # Arrow-based Intent（既存）
│   ├── FreerArrow.purs     # Arrow 実装（既存）
│   └── Vocabulary/
│       ├── SubjectF.purs   # 新規
│       ├── ThingF.purs     # 新規
│       ├── RelationF.purs  # 新規
│       ├── ContractF.purs  # 新規
│       ├── NoemaF.purs     # 新規（統合）
│       └── Constructors.purs # 新規
│
└── Cognition/
    └── Handler.purs        # Handler（後続タスク）
```

---

## 実装順序

1. `Core/Locus.purs` - 基本識別子
2. `Core/World.purs` - 法座標
3. `Vocabulary/SubjectF.purs`
4. `Vocabulary/ThingF.purs`
5. `Vocabulary/RelationF.purs`
6. `Vocabulary/ContractF.purs`
7. `Vocabulary/NoemaF.purs` - 統合
8. `Vocabulary/Constructors.purs` - スマートコンストラクタ
9. テスト

---

## 注意事項

### Arrow Effects の維持

- `ArrowChoice` は実装しない（分岐禁止）
- 分岐は Handler（Cognition）の責務
- Intent は静的構造のみ

### Sediment（沈殿）

- すべての状態変更は Sediment として追記
- UPDATE は禁止、INSERT のみ
- Snapshot は Sediment の畳み込み

### 時間構造（Husserl）

- Retention: 過去の把持（Snapshot）
- Primal: 現在（最新の Sediment 積分値）
- Protention: 未来の予持（Alarm と連動）

### 関係の Source of Truth

- 所有権等の Master Data は Thing を包摂する Subject が保持
- Container の Contents は View（キャッシュ）

---

## テスト方針

1. **型レベルのテスト**: コンパイルが通ること
2. **Functor 則**: 各語彙が Functor 則を満たすこと
3. **Arrow 則**: Intent が Arrow 則を満たすこと（既存テスト）
4. **ビジネスシナリオ**: 
   - 売買契約の成立と履行
   - 委託販売
   - リース・レンタル
   - 所有権留保
   - 質権・留置権

---

## 参考資料

- `/mnt/user-data/uploads/design-principles.md` - 設計原理
- `/mnt/user-data/uploads/freer-arrow-design.md` - Arrow 設計
- `/mnt/user-data/uploads/architecture.md` - アーキテクチャ
- 会話トランスクリプト: Vocabulary 設計の詳細な議論
