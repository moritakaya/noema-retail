-- | Noema ContractF Test
-- |
-- | ContractF（契約）モジュールのテスト。
-- |
-- | ## テスト対象
-- |
-- | - ContractStatus の等値性と Show
-- | - ObligationKind, ObligationStatus の等値性
-- | - ContractRelationKind の等値性と Show
-- | - Obligation, ContractState レコードの構造
module Test.ContractF where

import Prelude

import Data.Foldable (and)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

import Noema.Topos.Situs (Timestamp(..), mkSubjectId, mkThingId, mkContractId)
import Noema.Vorzeichnung.Vocabulary.ContractF
  ( ContractStatus(..)
  , ObligationKind(..)
  , ObligationStatus(..)
  , Obligation
  , ContractParties
  , ContractState
  , ContractRelationKind(..)
  , ContractRelation
  )

-- ============================================================
-- ContractStatus テスト
-- ============================================================

-- | ContractStatus の等値性
test_contract_status_equality :: Effect Boolean
test_contract_status_equality = do
  pure $
    Draft == Draft &&
    Proposed == Proposed &&
    Accepted == Accepted &&
    InProgress == InProgress &&
    Fulfilled == Fulfilled &&
    Cancelled == Cancelled &&
    Disputed == Disputed &&
    Draft /= Proposed &&
    Accepted /= Cancelled

-- | ContractStatus の Show
test_contract_status_show :: Effect Boolean
test_contract_status_show = do
  let
    results =
      [ show Draft == "Draft"
      , show Proposed == "Proposed"
      , show Accepted == "Accepted"
      , show InProgress == "InProgress"
      , show Fulfilled == "Fulfilled"
      , show Cancelled == "Cancelled"
      , show Disputed == "Disputed"
      ]

  pure (and results)

-- ============================================================
-- ObligationKind テスト
-- ============================================================

-- | ObligationKind の等値性
test_obligation_kind_equality :: Effect Boolean
test_obligation_kind_equality = do
  pure $
    Transfer_ == Transfer_ &&
    Payment == Payment &&
    Perform == Perform &&
    Refrain == Refrain &&
    Transfer_ /= Payment &&
    Perform /= Refrain

-- | ObligationKind の Show
test_obligation_kind_show :: Effect Boolean
test_obligation_kind_show = do
  let
    results =
      [ show Transfer_ == "Transfer"
      , show Payment == "Payment"
      , show Perform == "Perform"
      , show Refrain == "Refrain"
      ]

  pure (and results)

-- ============================================================
-- ObligationStatus テスト
-- ============================================================

-- | ObligationStatus の等値性
test_obligation_status_equality :: Effect Boolean
test_obligation_status_equality = do
  pure $
    Pending == Pending &&
    Fulfilled_ == Fulfilled_ &&
    Breached == Breached &&
    Waived == Waived &&
    Pending /= Fulfilled_ &&
    Breached /= Waived

-- | ObligationStatus の Show
test_obligation_status_show :: Effect Boolean
test_obligation_status_show = do
  let
    results =
      [ show Pending == "Pending"
      , show Fulfilled_ == "Fulfilled"
      , show Breached == "Breached"
      , show Waived == "Waived"
      ]

  pure (and results)

-- ============================================================
-- ContractRelationKind テスト
-- ============================================================

-- | ContractRelationKind の等値性
test_contract_relation_kind_equality :: Effect Boolean
test_contract_relation_kind_equality = do
  pure $
    Prerequisite == Prerequisite &&
    Subordinate == Subordinate &&
    Consideration == Consideration &&
    Security == Security &&
    Amendment == Amendment &&
    Termination == Termination &&
    Prerequisite /= Subordinate &&
    Amendment /= Termination

-- | ContractRelationKind の Show
test_contract_relation_kind_show :: Effect Boolean
test_contract_relation_kind_show = do
  let
    results =
      [ show Prerequisite == "Prerequisite"
      , show Subordinate == "Subordinate"
      , show Consideration == "Consideration"
      , show Security == "Security"
      , show Amendment == "Amendment"
      , show Termination == "Termination"
      ]

  pure (and results)

-- ============================================================
-- Obligation テスト
-- ============================================================

-- | Obligation の構造
test_obligation_structure :: Effect Boolean
test_obligation_structure = do
  let
    sid1 = mkSubjectId "seller-001"
    sid2 = mkSubjectId "buyer-001"
    tid = mkThingId "thing-001"
    ts = Timestamp 1704067200000.0

    obligation :: Obligation
    obligation =
      { id: "obl-001"
      , kind: Transfer_
      , debtor: sid1
      , creditor: sid2
      , thingRef: Just tid
      , amount: Nothing
      , dueDate: Just ts
      , status: Pending
      }

  pure $
    obligation.id == "obl-001" &&
    obligation.kind == Transfer_ &&
    obligation.debtor == sid1 &&
    obligation.creditor == sid2 &&
    obligation.thingRef == Just tid &&
    obligation.amount == Nothing &&
    obligation.dueDate == Just ts &&
    obligation.status == Pending

-- | Payment Obligation
test_payment_obligation :: Effect Boolean
test_payment_obligation = do
  let
    obligation :: Obligation
    obligation =
      { id: "obl-002"
      , kind: Payment
      , debtor: mkSubjectId "buyer-001"
      , creditor: mkSubjectId "seller-001"
      , thingRef: Nothing
      , amount: Just 10000.0
      , dueDate: Nothing
      , status: Pending
      }

  pure $
    obligation.kind == Payment &&
    obligation.amount == Just 10000.0 &&
    obligation.thingRef == Nothing

-- ============================================================
-- ContractParties テスト
-- ============================================================

-- | ContractParties の構造
test_contract_parties_structure :: Effect Boolean
test_contract_parties_structure = do
  let
    partyA = mkSubjectId "company-001"
    partyB = mkSubjectId "company-002"

    parties :: ContractParties
    parties =
      { partyA
      , partyB
      }

  pure $
    parties.partyA == partyA &&
    parties.partyB == partyB

-- ============================================================
-- ContractState テスト
-- ============================================================

-- | ContractState の構造
test_contract_state_structure :: Effect Boolean
test_contract_state_structure = do
  let
    cid = mkContractId "contract-001"
    partyA = mkSubjectId "seller-001"
    partyB = mkSubjectId "buyer-001"
    ts = Timestamp 1704067200000.0

    state :: ContractState
    state =
      { id: cid
      , parties: { partyA, partyB }
      , terms: []
      , thingRefs: []
      , status: Proposed
      , obligations: []
      , createdAt: ts
      , updatedAt: ts
      }

  pure $
    state.id == cid &&
    state.parties.partyA == partyA &&
    state.parties.partyB == partyB &&
    state.status == Proposed &&
    state.obligations == [] &&
    state.createdAt == ts

-- ============================================================
-- ContractRelation テスト
-- ============================================================

-- | ContractRelation の構造
test_contract_relation_structure :: Effect Boolean
test_contract_relation_structure = do
  let
    from = mkContractId "contract-001"
    to = mkContractId "contract-002"

    relation :: ContractRelation
    relation =
      { from
      , to
      , kind: Subordinate
      , description: Just "Main contract subordinates guarantee"
      }

  pure $
    relation.from == from &&
    relation.to == to &&
    relation.kind == Subordinate &&
    relation.description == Just "Main contract subordinates guarantee"

-- | ContractRelation without description
test_contract_relation_no_description :: Effect Boolean
test_contract_relation_no_description = do
  let
    relation :: ContractRelation
    relation =
      { from: mkContractId "contract-001"
      , to: mkContractId "contract-003"
      , kind: Amendment
      , description: Nothing
      }

  pure $
    relation.kind == Amendment &&
    relation.description == Nothing

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema ContractF Test ==="
  log ""

  log "--- ContractStatus ---"

  log "ContractStatus equality"
  r1 <- test_contract_status_equality
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log "ContractStatus show"
  r2 <- test_contract_status_show
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ObligationKind ---"

  log "ObligationKind equality"
  r3 <- test_obligation_kind_equality
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log "ObligationKind show"
  r4 <- test_obligation_kind_show
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ObligationStatus ---"

  log "ObligationStatus equality"
  r5 <- test_obligation_status_equality
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log "ObligationStatus show"
  r6 <- test_obligation_status_show
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ContractRelationKind ---"

  log "ContractRelationKind equality"
  r7 <- test_contract_relation_kind_equality
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log "ContractRelationKind show"
  r8 <- test_contract_relation_kind_show
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Obligation ---"

  log "Obligation structure"
  r9 <- test_obligation_structure
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log "Payment Obligation"
  r10 <- test_payment_obligation
  log $ "  Result: " <> if r10 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ContractParties ---"

  log "ContractParties structure"
  r11 <- test_contract_parties_structure
  log $ "  Result: " <> if r11 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ContractState ---"

  log "ContractState structure"
  r12 <- test_contract_state_structure
  log $ "  Result: " <> if r12 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ContractRelation ---"

  log "ContractRelation structure"
  r13 <- test_contract_relation_structure
  log $ "  Result: " <> if r13 then "✓ PASS" else "✗ FAIL"

  log "ContractRelation without description"
  r14 <- test_contract_relation_no_description
  log $ "  Result: " <> if r14 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = and [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14]
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
