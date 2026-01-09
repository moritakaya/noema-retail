-- | Noema ThingF Test
-- |
-- | ThingF（意志を持たない物）モジュールのテスト。
-- |
-- | ## テスト対象
-- |
-- | - PropertyKey の等値性と順序
-- | - SitusChange の構造
-- | - ChangeReason の Show インスタンス
-- | - ThingSnapshot/ThingState の構造
module Test.ThingF where

import Prelude

import Data.Foldable (and)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Argonaut.Core (jsonNull)
import Effect (Effect)
import Effect.Console (log)

import Noema.Topos.Situs (SedimentId(..), Timestamp(..), mkSubjectId, mkThingId, mkContractId)
import Noema.Vorzeichnung.Vocabulary.ThingF
  ( PropertyKey(..)
  , ChangeReason(..)
  , SitusChange
  , ThingSnapshot
  , ThingState
  , ProtentionId(..)
  )

-- ============================================================
-- PropertyKey テスト
-- ============================================================

-- | PropertyKey の等値性
test_property_key_equality :: Effect Boolean
test_property_key_equality = do
  let
    k1 = PropertyKey "color"
    k2 = PropertyKey "color"
    k3 = PropertyKey "size"

  pure $ (k1 == k2) && (k1 /= k3)

-- | PropertyKey の順序
test_property_key_ordering :: Effect Boolean
test_property_key_ordering = do
  let
    k1 = PropertyKey "apple"
    k2 = PropertyKey "banana"
    k3 = PropertyKey "cherry"

  pure $ (k1 < k2) && (k2 < k3) && (k1 < k3)

-- | PropertyKey の Show
test_property_key_show :: Effect Boolean
test_property_key_show = do
  let
    k = PropertyKey "sku"

  -- String の Show はクォートを含む
  pure $ show k == "\"sku\""

-- ============================================================
-- ChangeReason テスト
-- ============================================================

-- | ChangeReason の等値性
test_change_reason_equality :: Effect Boolean
test_change_reason_equality = do
  let
    cid1 = mkContractId "contract-001"
    cid2 = mkContractId "contract-002"

    r1 = Sale cid1
    r2 = Sale cid1
    r3 = Sale cid2
    r4 = Transfer

  pure $ (r1 == r2) && (r1 /= r3) && (r1 /= r4) && (Transfer == Transfer)

-- | ChangeReason の Show
test_change_reason_show :: Effect Boolean
test_change_reason_show = do
  let
    cid = mkContractId "contract-001"

    results =
      [ show (Sale cid) == "(Sale (ContractId contract-001))"
      , show (Purchase cid) == "(Purchase (ContractId contract-001))"
      , show Transfer == "Transfer"
      , show (Return cid) == "(Return (ContractId contract-001))"
      , show (Adjustment "棚卸") == "(Adjustment 棚卸)"
      ]

  pure (and results)

-- ============================================================
-- SitusChange テスト
-- ============================================================

-- | SitusChange の構造
test_situs_change_structure :: Effect Boolean
test_situs_change_structure = do
  let
    fromSubject = mkSubjectId "warehouse-001"
    toSubject = mkSubjectId "store-001"
    cid = mkContractId "contract-001"

    change :: SitusChange
    change =
      { from: fromSubject
      , to: toSubject
      , reason: Sale cid
      , contractRef: Just cid
      }

  pure $
    change.from == fromSubject &&
    change.to == toSubject &&
    change.reason == Sale cid &&
    change.contractRef == Just cid

-- | SitusChange の contractRef なし
test_situs_change_no_contract :: Effect Boolean
test_situs_change_no_contract = do
  let
    change :: SitusChange
    change =
      { from: mkSubjectId "warehouse-001"
      , to: mkSubjectId "warehouse-002"
      , reason: Transfer
      , contractRef: Nothing
      }

  pure $ change.reason == Transfer && change.contractRef == Nothing

-- ============================================================
-- ThingSnapshot テスト
-- ============================================================

-- | ThingSnapshot の構造
test_thing_snapshot_structure :: Effect Boolean
test_thing_snapshot_structure = do
  let
    tid = mkThingId "item-001"
    sid = mkSubjectId "warehouse-001"
    ts = Timestamp 1704067200000.0
    sedId = SedimentId 42

    snapshot :: ThingSnapshot
    snapshot =
      { thingId: tid
      , timestamp: ts
      , properties: Map.singleton (PropertyKey "color") jsonNull
      , situs: sid
      , sedimentId: sedId
      }

  pure $
    snapshot.thingId == tid &&
    snapshot.timestamp == ts &&
    snapshot.situs == sid &&
    snapshot.sedimentId == sedId

-- ============================================================
-- ThingState テスト
-- ============================================================

-- | ThingState の構造
test_thing_state_structure :: Effect Boolean
test_thing_state_structure = do
  let
    tid = mkThingId "item-002"
    sid = mkSubjectId "store-001"
    ts = Timestamp 1718452800000.0

    state :: ThingState
    state =
      { thingId: tid
      , properties: Map.empty
      , situs: sid
      , lastModified: ts
      , protentions: []
      }

  pure $
    state.thingId == tid &&
    state.situs == sid &&
    state.lastModified == ts &&
    state.protentions == []

-- | ThingState with protentions
test_thing_state_with_protentions :: Effect Boolean
test_thing_state_with_protentions = do
  let
    pid1 = ProtentionId "protention-001"
    pid2 = ProtentionId "protention-002"

    state :: ThingState
    state =
      { thingId: mkThingId "item-003"
      , properties: Map.empty
      , situs: mkSubjectId "warehouse-001"
      , lastModified: Timestamp 1718452800000.0
      , protentions: [pid1, pid2]
      }

  pure $ state.protentions == [pid1, pid2]

-- ============================================================
-- ProtentionId テスト
-- ============================================================

-- | ProtentionId の等値性
test_protention_id_equality :: Effect Boolean
test_protention_id_equality = do
  let
    p1 = ProtentionId "prot-001"
    p2 = ProtentionId "prot-001"
    p3 = ProtentionId "prot-002"

  pure $ (p1 == p2) && (p1 /= p3)

-- | ProtentionId の順序
test_protention_id_ordering :: Effect Boolean
test_protention_id_ordering = do
  let
    p1 = ProtentionId "a"
    p2 = ProtentionId "b"
    p3 = ProtentionId "c"

  pure $ (p1 < p2) && (p2 < p3)

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema ThingF Test ==="
  log ""

  log "--- PropertyKey ---"

  log "PropertyKey equality"
  r1 <- test_property_key_equality
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log "PropertyKey ordering"
  r2 <- test_property_key_ordering
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log "PropertyKey show"
  r3 <- test_property_key_show
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ChangeReason ---"

  log "ChangeReason equality"
  r4 <- test_change_reason_equality
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log "ChangeReason show"
  r5 <- test_change_reason_show
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- SitusChange ---"

  log "SitusChange structure"
  r6 <- test_situs_change_structure
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log "SitusChange without contract"
  r7 <- test_situs_change_no_contract
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ThingSnapshot ---"

  log "ThingSnapshot structure"
  r8 <- test_thing_snapshot_structure
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ThingState ---"

  log "ThingState structure"
  r9 <- test_thing_state_structure
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log "ThingState with protentions"
  r10 <- test_thing_state_with_protentions
  log $ "  Result: " <> if r10 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ProtentionId ---"

  log "ProtentionId equality"
  r11 <- test_protention_id_equality
  log $ "  Result: " <> if r11 then "✓ PASS" else "✗ FAIL"

  log "ProtentionId ordering"
  r12 <- test_protention_id_ordering
  log $ "  Result: " <> if r12 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = and [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
