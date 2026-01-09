-- | Noema Vocabulary: ContractF（契約）
-- |
-- | 契約のライフサイクルと義務の管理を定義する。
-- | 契約間の関係（前提、従属、対価、担保、変更、解除）も含む。
-- |
-- | ## 圏論的位置づけ
-- |
-- | ContractF は規定の圏の操作を定義する Functor。
-- | Contract は Nomos（大域意志）に依拠する。
module Noema.Vorzeichnung.Vocabulary.ContractF
  ( ContractStatus(..)
  , ObligationKind(..)
  , ObligationStatus(..)
  , Obligation
  , ObligationDef
  , FulfillmentProof
  , ContractParties
  , Term
  , ContractProposal
  , ContractState
  , RejectReason
  , CancelReason
  , ContractRelationKind(..)
  , ContractRelation
  , ContractGraph
  , ContractF(..)
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Argonaut.Core (Json)
import Noema.Topos.Situs
  ( ThingId, SubjectId, ContractId, SedimentId, Timestamp )
import Noema.Topos.Nomos (NomosReference)

-- | 契約の状態
data ContractStatus
  = Draft        -- 下書き
  | Proposed     -- 提案済み
  | Accepted     -- 受諾済み
  | InProgress   -- 履行中
  | Fulfilled    -- 履行完了
  | Cancelled    -- 取消済み
  | Disputed     -- 紛争中

derive instance eqContractStatus :: Eq ContractStatus

instance showContractStatus :: Show ContractStatus where
  show Draft = "Draft"
  show Proposed = "Proposed"
  show Accepted = "Accepted"
  show InProgress = "InProgress"
  show Fulfilled = "Fulfilled"
  show Cancelled = "Cancelled"
  show Disputed = "Disputed"

-- | 義務の種類
data ObligationKind
  = Transfer_     -- Thing の移転義務（Transfer は予約語なので避ける）
  | Payment       -- 支払義務
  | Perform       -- 役務提供義務
  | Refrain       -- 不作為義務

derive instance eqObligationKind :: Eq ObligationKind

instance showObligationKind :: Show ObligationKind where
  show Transfer_ = "Transfer"
  show Payment = "Payment"
  show Perform = "Perform"
  show Refrain = "Refrain"

-- | 義務の状態
data ObligationStatus
  = Pending       -- 未履行
  | Fulfilled_    -- 履行済み
  | Breached      -- 不履行
  | Waived        -- 免除

derive instance eqObligationStatus :: Eq ObligationStatus

instance showObligationStatus :: Show ObligationStatus where
  show Pending = "Pending"
  show Fulfilled_ = "Fulfilled"
  show Breached = "Breached"
  show Waived = "Waived"

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

-- | 義務の定義（作成時）
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

-- | 契約条項（任意の JSON）
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
  = Prerequisite    -- 前提（B は A がないと成立しない）
  | Subordinate     -- 従属（A 終了で B も終了）
  | Consideration   -- 対価（A の履行が B の対価）
  | Security        -- 担保（B は A の履行を担保）
  | Amendment       -- 変更（B は A を変更）
  | Termination     -- 解除（B は A を解除）

derive instance eqContractRelationKind :: Eq ContractRelationKind

instance showContractRelationKind :: Show ContractRelationKind where
  show Prerequisite = "Prerequisite"
  show Subordinate = "Subordinate"
  show Consideration = "Consideration"
  show Security = "Security"
  show Amendment = "Amendment"
  show Termination = "Termination"

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

-- | Functor instance
instance functorContractF :: Functor (ContractF i) where
  map f = case _ of
    ProposeContract toProposal k -> ProposeContract toProposal (f <<< k)
    AcceptContract cid toUnit k -> AcceptContract cid toUnit (f <<< k)
    RejectContract cid toReason k -> RejectContract cid toReason (f <<< k)
    CancelContract cid toReason k -> CancelContract cid toReason (f <<< k)
    GetContract cid toUnit k -> GetContract cid toUnit (f <<< k)
    GetContractsByParty sid toUnit k -> GetContractsByParty sid toUnit (f <<< k)
    AddObligation cid toDef k -> AddObligation cid toDef (f <<< k)
    FulfillObligation oid toProof k -> FulfillObligation oid toProof (f <<< k)
    GetObligations cid toUnit k -> GetObligations cid toUnit (f <<< k)
    GetPendingObligations sid toUnit k -> GetPendingObligations sid toUnit (f <<< k)
    LinkContracts toRelation k -> LinkContracts toRelation (f <<< k)
    GetLinkedContracts cid kind toUnit k -> GetLinkedContracts cid kind toUnit (f <<< k)
    GetContractChain cid toUnit k -> GetContractChain cid toUnit (f <<< k)
