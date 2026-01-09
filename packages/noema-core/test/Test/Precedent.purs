-- | Noema Precedent Test
-- |
-- | Precedent（判例）モジュールのテスト。
-- |
-- | ## テスト対象
-- |
-- | - PrecedentRecord の作成
-- | - PrecedentLog の操作（追加、検索、カウント）
-- | - verifyConnectionWithPrecedent の判定ロジック
module Test.Precedent where

import Prelude

import Data.Argonaut.Core (jsonNull)
import Data.Foldable (and)
import Effect (Effect)
import Effect.Console (log)

import Noema.Topos.Situs (Timestamp(..))
import Noema.Topos.Nomos (NomosVersion(..), ConnectionType(..), mkWorld)
import Noema.Sedimentation.Precedent
  ( mkPrecedentRecord
  , emptyPrecedentLog
  , addPrecedent
  , findPrecedents
  , precedentCount
  , verifyConnectionWithPrecedent
  )

-- ============================================================
-- PrecedentRecord テスト
-- ============================================================

-- | PrecedentRecord の作成
test_precedent_record_creation :: Effect Boolean
test_precedent_record_creation = do
  let
    nv = NomosVersion "1.0.0"
    ts = Timestamp 1704067200000.0
    world = mkWorld nv ts

    record = mkPrecedentRecord
      "staging-001"
      nv
      "Version mismatch"
      ts
      jsonNull
      world

  pure $
    record.stagingId == "staging-001" &&
    record.nomosVersion == nv &&
    record.rejectionReason == "Version mismatch" &&
    record.rejectedAt == ts

-- ============================================================
-- PrecedentLog テスト
-- ============================================================

-- | 空の PrecedentLog
test_empty_precedent_log :: Effect Boolean
test_empty_precedent_log = do
  let plog = emptyPrecedentLog

  pure $
    precedentCount plog == 0 &&
    plog.lastUpdated == Timestamp 0.0

-- | PrecedentLog への追加
test_add_precedent :: Effect Boolean
test_add_precedent = do
  let
    nv = NomosVersion "1.0.0"
    ts1 = Timestamp 1704067200000.0
    ts2 = Timestamp 1704153600000.0
    world = mkWorld nv ts1

    record1 = mkPrecedentRecord "staging-001" nv "Reason A" ts1 jsonNull world
    record2 = mkPrecedentRecord "staging-002" nv "Reason B" ts2 jsonNull world

    plog0 = emptyPrecedentLog
    plog1 = addPrecedent record1 plog0
    plog2 = addPrecedent record2 plog1

  pure $
    precedentCount plog1 == 1 &&
    precedentCount plog2 == 2 &&
    plog2.lastUpdated == ts2

-- | PrecedentLog の検索
test_find_precedents :: Effect Boolean
test_find_precedents = do
  let
    nv = NomosVersion "1.0.0"
    ts = Timestamp 1704067200000.0
    world = mkWorld nv ts

    record1 = mkPrecedentRecord "staging-001" nv "Reason A" ts jsonNull world
    record2 = mkPrecedentRecord "staging-002" nv "Reason B" ts jsonNull world
    record3 = mkPrecedentRecord "staging-003" nv "Reason A" ts jsonNull world

    plog = addPrecedent record3
         $ addPrecedent record2
         $ addPrecedent record1 emptyPrecedentLog

    foundA = findPrecedents "Reason A" plog
    foundB = findPrecedents "Reason B" plog
    foundC = findPrecedents "Reason C" plog

  -- foundA should find 2 records (record1 and record3)
  -- foundB should find 1 record (record2)
  -- foundC should find 0 records
  pure $
    (case foundA of
      [_, _] -> true
      _ -> false) &&
    (case foundB of
      [_] -> true
      _ -> false) &&
    (case foundC of
      [] -> true
      _ -> false)

-- ============================================================
-- verifyConnectionWithPrecedent テスト
-- ============================================================

-- | 判例なしで Flat
test_connection_flat_no_precedent :: Effect Boolean
test_connection_flat_no_precedent = do
  let
    nv = NomosVersion "1.0.0"
    ts = Timestamp 1704067200000.0
    world = mkWorld nv ts

    plog = emptyPrecedentLog
    result = verifyConnectionWithPrecedent plog world world

  pure $ result == Flat

-- | 判例なしで Curved（バージョン不一致）
test_connection_curved_version_mismatch :: Effect Boolean
test_connection_curved_version_mismatch = do
  let
    nv1 = NomosVersion "1.0.0"
    nv2 = NomosVersion "2.0.0"
    ts = Timestamp 1704067200000.0
    world1 = mkWorld nv1 ts
    world2 = mkWorld nv2 ts

    plog = emptyPrecedentLog
    result = verifyConnectionWithPrecedent plog world1 world2

  pure $ case result of
    Curved _ -> true
    _ -> false

-- | 判例蓄積による Flat → Curved 昇格
test_connection_flat_to_curved_with_precedents :: Effect Boolean
test_connection_flat_to_curved_with_precedents = do
  let
    nv = NomosVersion "1.0.0"
    ts = Timestamp 1704067200000.0
    world = mkWorld nv ts

    -- 3件の判例を追加（閾値に達する）
    record1 = mkPrecedentRecord "staging-001" nv "Reason" ts jsonNull world
    record2 = mkPrecedentRecord "staging-002" nv "Reason" ts jsonNull world
    record3 = mkPrecedentRecord "staging-003" nv "Reason" ts jsonNull world

    plog = addPrecedent record3
         $ addPrecedent record2
         $ addPrecedent record1 emptyPrecedentLog

    result = verifyConnectionWithPrecedent plog world world

  -- 本来 Flat だが、判例が3件あるので Curved に昇格
  pure $ case result of
    Curved "Multiple precedents suggest caution" -> true
    _ -> false

-- | 判例蓄積による Curved → Critical 昇格
test_connection_curved_to_critical_with_precedents :: Effect Boolean
test_connection_curved_to_critical_with_precedents = do
  let
    nv1 = NomosVersion "1.0.0"
    nv2 = NomosVersion "2.0.0"
    ts = Timestamp 1704067200000.0
    world1 = mkWorld nv1 ts
    world2 = mkWorld nv2 ts

    -- 3件の判例を nv1 で追加
    record1 = mkPrecedentRecord "staging-001" nv1 "Reason" ts jsonNull world1
    record2 = mkPrecedentRecord "staging-002" nv1 "Reason" ts jsonNull world1
    record3 = mkPrecedentRecord "staging-003" nv1 "Reason" ts jsonNull world1

    plog = addPrecedent record3
         $ addPrecedent record2
         $ addPrecedent record1 emptyPrecedentLog

    result = verifyConnectionWithPrecedent plog world1 world2

  -- 本来 Curved だが、判例が3件あるので Critical に昇格
  pure $ case result of
    Critical _ -> true
    _ -> false

-- | 異なるバージョンの判例は影響しない
test_connection_different_version_precedents :: Effect Boolean
test_connection_different_version_precedents = do
  let
    nv1 = NomosVersion "1.0.0"
    nv2 = NomosVersion "2.0.0"
    ts = Timestamp 1704067200000.0
    world1 = mkWorld nv1 ts
    world2 = mkWorld nv2 ts

    -- nv2 での判例（nv1 の検証には影響しない）
    record1 = mkPrecedentRecord "staging-001" nv2 "Reason" ts jsonNull world2
    record2 = mkPrecedentRecord "staging-002" nv2 "Reason" ts jsonNull world2
    record3 = mkPrecedentRecord "staging-003" nv2 "Reason" ts jsonNull world2

    plog = addPrecedent record3
         $ addPrecedent record2
         $ addPrecedent record1 emptyPrecedentLog

    result = verifyConnectionWithPrecedent plog world1 world1

  -- nv2 の判例は nv1 の検証に影響しないので Flat のまま
  pure $ result == Flat

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema Precedent Test ==="
  log ""

  log "--- PrecedentRecord ---"

  log "PrecedentRecord creation"
  r1 <- test_precedent_record_creation
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- PrecedentLog ---"

  log "Empty PrecedentLog"
  r2 <- test_empty_precedent_log
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log "Add precedent"
  r3 <- test_add_precedent
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log "Find precedents"
  r4 <- test_find_precedents
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- verifyConnectionWithPrecedent ---"

  log "Flat with no precedent"
  r5 <- test_connection_flat_no_precedent
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log "Curved with version mismatch"
  r6 <- test_connection_curved_version_mismatch
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log "Flat to Curved with precedents"
  r7 <- test_connection_flat_to_curved_with_precedents
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log "Curved to Critical with precedents"
  r8 <- test_connection_curved_to_critical_with_precedents
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log "Different version precedents"
  r9 <- test_connection_different_version_precedents
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = and [r1, r2, r3, r4, r5, r6, r7, r8, r9]
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
