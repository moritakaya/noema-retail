-- | Noema Vocabulary: Constructors（スマートコンストラクタ）
-- |
-- | 各語彙の操作を Intent として持ち上げるスマートコンストラクタを提供。
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | import Noema.Vorzeichnung.Vocabulary.Constructors
-- |
-- | -- Subject を作成
-- | createNewSubject :: NoemaIntent SubjectInit SubjectId
-- | createNewSubject = createSubject
-- |
-- | -- Thing の状態を取得
-- | getInventory :: ThingId -> NoemaIntent Unit ThingState
-- | getInventory tid = getThingState tid
-- | ```
module Noema.Vorzeichnung.Vocabulary.Constructors
  ( -- * Subject constructors
    createSubject
  , getSubject
  , getSubjectsByKind
  , updateSubject
  , sendIntent
  , confirmReceipt
    -- * Thing constructors
  , getProperty
  , setProperty
  , getSitus
  , recordSitusChange
  , getRetention
  , getRetentionRange
  , getPrimal
  , registerProtention
  , getProtentions
  , realizeProtention
  , cancelProtention
    -- * Relation constructors
  , getRelation
  , getRelationsFrom
  , getRelationsTo
  , addRelation
  , removeRelation
  , updateRelationMetadata
  , recordOwnershipTransfer
  , getContents
  , getObservedThings
  , getIntendedThings
    -- * Contract constructors
  , proposeContract
  , acceptContract
  , rejectContract
  , cancelContract
  , getContract
  , getContractsByParty
  , addObligation
  , fulfillObligation
  , getObligations
  , getPendingObligations
  , linkContracts
  , getLinkedContracts
  , getContractChain
  ) where

import Prelude

import Data.Maybe (Maybe)
import Noema.Vorzeichnung.Intent (Intent, liftEffect)
import Noema.Vorzeichnung.Vocabulary.NoemaF (NoemaF, inSubject, inThing, inRelation, inContract)
import Noema.Topos.Situs
  ( SubjectId, ThingId, ContractId, RelationId, SedimentId, Timestamp )

import Noema.Vorzeichnung.Vocabulary.SubjectF as S
import Noema.Vorzeichnung.Vocabulary.ThingF as T
import Noema.Vorzeichnung.Vocabulary.RelationF as R
import Noema.Vorzeichnung.Vocabulary.ContractF as C

-- ============================================================
-- Subject Constructors
-- ============================================================

-- | Subject を作成
createSubject :: Intent (NoemaF S.SubjectInit) S.SubjectInit SubjectId
createSubject = liftEffect (inSubject (S.CreateSubject identity identity))

-- | Subject を取得
getSubject :: SubjectId -> Intent (NoemaF Unit) Unit S.SubjectState
getSubject sid = liftEffect (inSubject (S.GetSubject sid identity identity))

-- | 種別で Subject を取得
getSubjectsByKind :: S.SubjectKind -> Intent (NoemaF Unit) Unit (Array S.SubjectState)
getSubjectsByKind kind = liftEffect (inSubject (S.GetSubjectsByKind kind identity identity))

-- | Subject を更新
updateSubject :: SubjectId -> Intent (NoemaF S.SubjectPatch) S.SubjectPatch SedimentId
updateSubject sid = liftEffect (inSubject (S.UpdateSubject sid identity identity))

-- | Intent を送信
sendIntent :: SubjectId -> Intent (NoemaF S.IntentEnvelope) S.IntentEnvelope S.Receipt
sendIntent sid = liftEffect (inSubject (S.SendIntent sid identity identity))

-- | 受領証を確認
confirmReceipt :: String -> Intent (NoemaF Unit) Unit Unit
confirmReceipt rid = liftEffect (inSubject (S.ConfirmReceipt rid identity identity))

-- ============================================================
-- Thing Constructors
-- ============================================================

-- | Property を取得
getProperty :: ThingId -> T.PropertyKey -> Intent (NoemaF Unit) Unit T.PropertyValue
getProperty tid key = liftEffect (inThing (T.GetProperty tid key identity identity))

-- | Property を設定
setProperty :: ThingId -> T.PropertyKey -> Intent (NoemaF T.PropertyValue) T.PropertyValue SedimentId
setProperty tid key = liftEffect (inThing (T.SetProperty tid key identity identity))

-- | Thing の位置（situs）を取得
getSitus :: ThingId -> Intent (NoemaF Unit) Unit SubjectId
getSitus tid = liftEffect (inThing (T.GetSitus tid identity identity))

-- | 位置変更を記録
recordSitusChange :: ThingId -> Intent (NoemaF T.SitusChange) T.SitusChange SedimentId
recordSitusChange tid = liftEffect (inThing (T.RecordSitusChange tid identity identity))

-- | 過去の状態（把持）を取得
getRetention :: ThingId -> Timestamp -> Intent (NoemaF Unit) Unit T.ThingSnapshot
getRetention tid ts = liftEffect (inThing (T.GetRetention tid ts identity identity))

-- | 時間範囲で Sediment を取得
getRetentionRange :: ThingId -> T.TimeRange -> Intent (NoemaF Unit) Unit (Array T.Sediment)
getRetentionRange tid range = liftEffect (inThing (T.GetRetentionRange tid range identity identity))

-- | 現在の状態（原印象）を取得
getPrimal :: ThingId -> Intent (NoemaF Unit) Unit T.ThingState
getPrimal tid = liftEffect (inThing (T.GetPrimal tid identity identity))

-- | 予持を登録
registerProtention :: ThingId -> Intent (NoemaF T.PendingIntent) T.PendingIntent T.ProtentionId
registerProtention tid = liftEffect (inThing (T.RegisterProtention tid identity identity))

-- | 予持一覧を取得
getProtentions :: ThingId -> Intent (NoemaF Unit) Unit (Array T.PendingIntent)
getProtentions tid = liftEffect (inThing (T.GetProtentions tid identity identity))

-- | 予持を実現
realizeProtention :: T.ProtentionId -> Intent (NoemaF Unit) Unit SedimentId
realizeProtention pid = liftEffect (inThing (T.RealizeProtention pid identity identity))

-- | 予持をキャンセル
cancelProtention :: T.ProtentionId -> Intent (NoemaF Unit) Unit Unit
cancelProtention pid = liftEffect (inThing (T.CancelProtention pid identity identity))

-- ============================================================
-- Relation Constructors
-- ============================================================

-- | 関係を取得
getRelation :: RelationId -> Intent (NoemaF Unit) Unit (Maybe R.Relation)
getRelation rid = liftEffect (inRelation (R.GetRelation rid identity identity))

-- | Subject から出る関係を取得
getRelationsFrom :: SubjectId -> R.RelationKind -> Intent (NoemaF Unit) Unit (Array R.Relation)
getRelationsFrom sid kind = liftEffect (inRelation (R.GetRelationsFrom sid kind identity identity))

-- | Thing への関係を取得
getRelationsTo :: ThingId -> R.RelationKind -> Intent (NoemaF Unit) Unit (Array R.Relation)
getRelationsTo tid kind = liftEffect (inRelation (R.GetRelationsTo tid kind identity identity))

-- | 関係を追加
addRelation :: Intent (NoemaF R.RelationInit) R.RelationInit RelationId
addRelation = liftEffect (inRelation (R.AddRelation identity identity))

-- | 関係を削除
removeRelation :: RelationId -> Intent (NoemaF Unit) Unit SedimentId
removeRelation rid = liftEffect (inRelation (R.RemoveRelation rid identity identity))

-- | 関係のメタデータを更新
updateRelationMetadata :: RelationId -> Intent (NoemaF R.RelationMetadata) R.RelationMetadata SedimentId
updateRelationMetadata rid = liftEffect (inRelation (R.UpdateRelationMetadata rid identity identity))

-- | 所有権移転を記録
recordOwnershipTransfer :: Intent (NoemaF R.OwnershipTransfer) R.OwnershipTransfer SedimentId
recordOwnershipTransfer = liftEffect (inRelation (R.RecordOwnershipTransfer identity identity))

-- | Subject の Contents を取得
getContents :: SubjectId -> Intent (NoemaF Unit) Unit (Array ThingId)
getContents sid = liftEffect (inRelation (R.GetContents sid identity identity))

-- | 観測された Thing を取得
getObservedThings :: SubjectId -> R.ObserverContext -> Intent (NoemaF Unit) Unit (Array R.ThingView)
getObservedThings sid ctx = liftEffect (inRelation (R.GetObservedThings sid ctx identity identity))

-- | 意図された Thing を取得
getIntendedThings :: SubjectId -> Intent (NoemaF Unit) Unit (Array R.IntentionView)
getIntendedThings sid = liftEffect (inRelation (R.GetIntendedThings sid identity identity))

-- ============================================================
-- Contract Constructors
-- ============================================================

-- | 契約を提案
proposeContract :: Intent (NoemaF C.ContractProposal) C.ContractProposal ContractId
proposeContract = liftEffect (inContract (C.ProposeContract identity identity))

-- | 契約を受諾
acceptContract :: ContractId -> Intent (NoemaF Unit) Unit SedimentId
acceptContract cid = liftEffect (inContract (C.AcceptContract cid identity identity))

-- | 契約を拒否
rejectContract :: ContractId -> Intent (NoemaF C.RejectReason) C.RejectReason SedimentId
rejectContract cid = liftEffect (inContract (C.RejectContract cid identity identity))

-- | 契約を取消
cancelContract :: ContractId -> Intent (NoemaF C.CancelReason) C.CancelReason SedimentId
cancelContract cid = liftEffect (inContract (C.CancelContract cid identity identity))

-- | 契約を取得
getContract :: ContractId -> Intent (NoemaF Unit) Unit C.ContractState
getContract cid = liftEffect (inContract (C.GetContract cid identity identity))

-- | 当事者の契約一覧を取得
getContractsByParty :: SubjectId -> Intent (NoemaF Unit) Unit (Array C.ContractState)
getContractsByParty sid = liftEffect (inContract (C.GetContractsByParty sid identity identity))

-- | 義務を追加
addObligation :: ContractId -> Intent (NoemaF C.ObligationDef) C.ObligationDef String
addObligation cid = liftEffect (inContract (C.AddObligation cid identity identity))

-- | 義務を履行
fulfillObligation :: String -> Intent (NoemaF C.FulfillmentProof) C.FulfillmentProof SedimentId
fulfillObligation oid = liftEffect (inContract (C.FulfillObligation oid identity identity))

-- | 契約の義務一覧を取得
getObligations :: ContractId -> Intent (NoemaF Unit) Unit (Array C.Obligation)
getObligations cid = liftEffect (inContract (C.GetObligations cid identity identity))

-- | 未履行の義務一覧を取得
getPendingObligations :: SubjectId -> Intent (NoemaF Unit) Unit (Array C.Obligation)
getPendingObligations sid = liftEffect (inContract (C.GetPendingObligations sid identity identity))

-- | 契約を関連付け
linkContracts :: Intent (NoemaF C.ContractRelation) C.ContractRelation SedimentId
linkContracts = liftEffect (inContract (C.LinkContracts identity identity))

-- | 関連する契約を取得
getLinkedContracts :: ContractId -> C.ContractRelationKind -> Intent (NoemaF Unit) Unit (Array ContractId)
getLinkedContracts cid kind = liftEffect (inContract (C.GetLinkedContracts cid kind identity identity))

-- | 契約チェーンを取得
getContractChain :: ContractId -> Intent (NoemaF Unit) Unit C.ContractGraph
getContractChain cid = liftEffect (inContract (C.GetContractChain cid identity identity))
