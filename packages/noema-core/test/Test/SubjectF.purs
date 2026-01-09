-- | Noema SubjectF Test
-- |
-- | SubjectF（意志を持つ主体）モジュールのテスト。
-- |
-- | ## テスト対象
-- |
-- | - SubjectKind の等値性と Show
-- | - SubjectState の構造
-- | - SubjectInit/SubjectPatch の構造
-- | - IntentEnvelope/Receipt の構造
module Test.SubjectF where

import Prelude

import Data.Argonaut.Core (jsonNull)
import Data.Foldable (and)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

import Noema.Topos.Situs (Timestamp(..), mkSubjectId)
import Noema.Topos.Nomos (NomosVersion(..), mkWorld, mkIntentContext)
import Noema.Vorzeichnung.Vocabulary.SubjectF
  ( SubjectKind(..)
  , SubjectState
  , SubjectInit
  , SubjectPatch
  , IntentEnvelope
  , Receipt
  )

-- ============================================================
-- SubjectKind テスト
-- ============================================================

-- | SubjectKind の等値性
test_subject_kind_equality :: Effect Boolean
test_subject_kind_equality = do
  let
    results =
      [ ContractParty == ContractParty
      , ThingHolder == ThingHolder
      , SystemAgent == SystemAgent
      , ContractParty /= ThingHolder
      , ThingHolder /= SystemAgent
      ]

  pure (and results)

-- | SubjectKind の Show
test_subject_kind_show :: Effect Boolean
test_subject_kind_show = do
  let
    results =
      [ show ContractParty == "ContractParty"
      , show ThingHolder == "ThingHolder"
      , show SystemAgent == "SystemAgent"
      ]

  pure (and results)

-- ============================================================
-- SubjectState テスト
-- ============================================================

-- | SubjectState の構造
test_subject_state_structure :: Effect Boolean
test_subject_state_structure = do
  let
    sid = mkSubjectId "subject-001"
    nv = NomosVersion "1.0.0"
    ts = Timestamp 1704067200000.0
    world = mkWorld nv ts

    state :: SubjectState
    state =
      { id: sid
      , kind: ThingHolder
      , world: world
      , lastActivity: ts
      }

  pure $
    state.id == sid &&
    state.kind == ThingHolder &&
    state.world.nomosVersion == nv &&
    state.lastActivity == ts

-- | SubjectState with ContractParty
test_subject_state_contract_party :: Effect Boolean
test_subject_state_contract_party = do
  let
    sid = mkSubjectId "seller-001"
    nv = NomosVersion "2.0.0"
    ts = Timestamp 1718452800000.0

    state :: SubjectState
    state =
      { id: sid
      , kind: ContractParty
      , world: mkWorld nv ts
      , lastActivity: ts
      }

  pure $ state.kind == ContractParty

-- | SubjectState with SystemAgent
test_subject_state_system_agent :: Effect Boolean
test_subject_state_system_agent = do
  let
    sid = mkSubjectId "cron-job-001"
    nv = NomosVersion "1.0.0"
    ts = Timestamp 1718452800000.0

    state :: SubjectState
    state =
      { id: sid
      , kind: SystemAgent
      , world: mkWorld nv ts
      , lastActivity: ts
      }

  pure $ state.kind == SystemAgent

-- ============================================================
-- SubjectInit テスト
-- ============================================================

-- | SubjectInit の構造
test_subject_init_structure :: Effect Boolean
test_subject_init_structure = do
  let
    nv = NomosVersion "1.0.0"
    ts = Timestamp 1704067200000.0
    world = mkWorld nv ts

    init :: SubjectInit
    init =
      { kind: ThingHolder
      , world: world
      }

  pure $
    init.kind == ThingHolder &&
    init.world.nomosVersion == nv

-- ============================================================
-- SubjectPatch テスト
-- ============================================================

-- | SubjectPatch with world update
test_subject_patch_with_world :: Effect Boolean
test_subject_patch_with_world = do
  let
    nv = NomosVersion "2.0.0"
    ts = Timestamp 1718452800000.0
    newWorld = mkWorld nv ts

    patch :: SubjectPatch
    patch = { world: Just newWorld }

  pure $ case patch.world of
    Just w -> w.nomosVersion == nv
    Nothing -> false

-- | SubjectPatch without world update
test_subject_patch_without_world :: Effect Boolean
test_subject_patch_without_world = do
  let
    patch :: SubjectPatch
    patch = { world: Nothing }

  pure $ case patch.world of
    Nothing -> true
    Just _ -> false

-- ============================================================
-- IntentEnvelope テスト
-- ============================================================

-- | IntentEnvelope の構造
test_intent_envelope_structure :: Effect Boolean
test_intent_envelope_structure = do
  let
    nv = NomosVersion "1.0.0"
    ts = Timestamp 1704067200000.0
    originWorld = mkWorld nv ts
    targetWorld = mkWorld nv ts
    ctx = mkIntentContext originWorld targetWorld

    envelope :: IntentEnvelope
    envelope =
      { body: jsonNull
      , context: ctx
      , seal: "signature-abc123"
      }

  pure $
    envelope.seal == "signature-abc123" &&
    envelope.context.origin.nomosVersion == nv

-- ============================================================
-- Receipt テスト
-- ============================================================

-- | Receipt の構造（accepted）
test_receipt_accepted :: Effect Boolean
test_receipt_accepted = do
  let
    ts = Timestamp 1704067200000.0

    receipt :: Receipt
    receipt =
      { id: "receipt-001"
      , timestamp: ts
      , accepted: true
      }

  pure $
    receipt.id == "receipt-001" &&
    receipt.timestamp == ts &&
    receipt.accepted == true

-- | Receipt の構造（rejected）
test_receipt_rejected :: Effect Boolean
test_receipt_rejected = do
  let
    ts = Timestamp 1704067200000.0

    receipt :: Receipt
    receipt =
      { id: "receipt-002"
      , timestamp: ts
      , accepted: false
      }

  pure $ receipt.accepted == false

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema SubjectF Test ==="
  log ""

  log "--- SubjectKind ---"

  log "SubjectKind equality"
  r1 <- test_subject_kind_equality
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log "SubjectKind show"
  r2 <- test_subject_kind_show
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- SubjectState ---"

  log "SubjectState structure"
  r3 <- test_subject_state_structure
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log "SubjectState ContractParty"
  r4 <- test_subject_state_contract_party
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log "SubjectState SystemAgent"
  r5 <- test_subject_state_system_agent
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- SubjectInit ---"

  log "SubjectInit structure"
  r6 <- test_subject_init_structure
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- SubjectPatch ---"

  log "SubjectPatch with world"
  r7 <- test_subject_patch_with_world
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log "SubjectPatch without world"
  r8 <- test_subject_patch_without_world
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- IntentEnvelope ---"

  log "IntentEnvelope structure"
  r9 <- test_intent_envelope_structure
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Receipt ---"

  log "Receipt accepted"
  r10 <- test_receipt_accepted
  log $ "  Result: " <> if r10 then "✓ PASS" else "✗ FAIL"

  log "Receipt rejected"
  r11 <- test_receipt_rejected
  log $ "  Result: " <> if r11 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = and [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11]
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
