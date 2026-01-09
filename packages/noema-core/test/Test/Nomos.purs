-- | Noema Nomos Test
-- |
-- | Nomos（法座標）モジュールのテスト。
-- |
-- | ## テスト対象
-- |
-- | - NomosVersion の等値性と順序
-- | - World, IntentContext の作成
-- | - Duration の作成
-- | - Connection の検証ロジック
module Test.Nomos where

import Prelude

import Data.Foldable (and)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Console (log)

import Noema.Topos.Situs (mkTimestamp)
import Noema.Topos.Nomos
  ( NomosVersion(..)
  , mkWorld
  , mkIntentContext
  , Duration(..)
  , mkDuration
  , ConnectionType(..)
  , verifyConnection
  , ContractTransition(..)
  )

-- ============================================================
-- NomosVersion テスト
-- ============================================================

-- | NomosVersion の等値性
test_version_equality :: Effect Boolean
test_version_equality = do
  let
    v1 = NomosVersion "1.0.0"
    v2 = NomosVersion "1.0.0"
    v3 = NomosVersion "2.0.0"

  pure $ (v1 == v2) && (v1 /= v3)

-- | NomosVersion の順序
test_version_ordering :: Effect Boolean
test_version_ordering = do
  let
    v1 = NomosVersion "1.0.0"
    v2 = NomosVersion "2.0.0"
    v3 = NomosVersion "1.5.0"

  -- 文字列順序による比較
  pure $ (v1 < v2) && (v3 < v2) && (v1 < v3)

-- | NomosVersion の Show
-- | Note: derive newtype instance から継承するため、
-- | String の Show（クォート付き）が使われる
test_version_show :: Effect Boolean
test_version_show = do
  let
    v = NomosVersion "1.0.0"

  -- String の Show はクォートを含む
  pure $ show v == "\"1.0.0\""

-- ============================================================
-- World テスト
-- ============================================================

-- | mkWorld で World を作成
test_mkWorld :: Effect Boolean
test_mkWorld = do
  let
    version = NomosVersion "1.0.0"
    timestamp = mkTimestamp 1704067200000.0  -- 2024-01-01T00:00:00Z
    world = mkWorld version timestamp

  pure $
    world.nomosVersion == version &&
    world.timestamp == timestamp &&
    world.region == Nothing

-- | World のフィールドアクセス
test_world_fields :: Effect Boolean
test_world_fields = do
  let
    version = NomosVersion "2.0.0"
    timestamp = mkTimestamp 1718452800000.0  -- 2024-06-15T12:00:00Z
    world = mkWorld version timestamp

  pure $
    unwrap world.nomosVersion == "2.0.0" &&
    world.timestamp == mkTimestamp 1718452800000.0

-- ============================================================
-- IntentContext テスト
-- ============================================================

-- | mkIntentContext で IntentContext を作成
test_mkIntentContext :: Effect Boolean
test_mkIntentContext = do
  let
    v1 = NomosVersion "1.0.0"
    v2 = NomosVersion "2.0.0"
    origin = mkWorld v1 (mkTimestamp 1704067200000.0)
    target = mkWorld v2 (mkTimestamp 1717200000000.0)
    ctx = mkIntentContext origin target

  pure $
    ctx.origin.nomosVersion == v1 &&
    ctx.target.nomosVersion == v2

-- ============================================================
-- Duration テスト
-- ============================================================

-- | mkDuration で Duration を作成
test_mkDuration :: Effect Boolean
test_mkDuration = do
  let
    d = mkDuration 3600000.0  -- 1時間（ミリ秒）

  pure $ unwrap d == 3600000.0

-- | Duration の等値性
test_duration_equality :: Effect Boolean
test_duration_equality = do
  let
    d1 = Duration 1000.0
    d2 = Duration 1000.0
    d3 = Duration 2000.0

  pure $ (d1 == d2) && (d1 /= d3)

-- | Duration の順序
test_duration_ordering :: Effect Boolean
test_duration_ordering = do
  let
    d1 = Duration 1000.0
    d2 = Duration 2000.0
    d3 = Duration 3000.0

  pure $ (d1 < d2) && (d2 < d3) && (d1 < d3)

-- ============================================================
-- Connection テスト
-- ============================================================

-- | 同一バージョンは Flat
test_connection_flat :: Effect Boolean
test_connection_flat = do
  let
    version = NomosVersion "1.0.0"
    w1 = mkWorld version (mkTimestamp 1704067200000.0)
    w2 = mkWorld version (mkTimestamp 1717200000000.0)
    connection = verifyConnection w1 w2

  pure $ connection == Flat

-- | 異なるバージョンは Curved
test_connection_curved :: Effect Boolean
test_connection_curved = do
  let
    v1 = NomosVersion "1.0.0"
    v2 = NomosVersion "2.0.0"
    w1 = mkWorld v1 (mkTimestamp 1704067200000.0)
    w2 = mkWorld v2 (mkTimestamp 1717200000000.0)
    connection = verifyConnection w1 w2

  pure $ case connection of
    Curved _ -> true
    _ -> false

-- | Connection の対称性（方向に依存しない判定結果のタイプ）
test_connection_type_consistency :: Effect Boolean
test_connection_type_consistency = do
  let
    v1 = NomosVersion "1.0.0"
    v2 = NomosVersion "2.0.0"
    w1 = mkWorld v1 (mkTimestamp 1704067200000.0)
    w2 = mkWorld v2 (mkTimestamp 1717200000000.0)

    conn12 = verifyConnection w1 w2
    conn21 = verifyConnection w2 w1

    -- 両方とも Curved であるべき（異なるバージョン間）
    isCurved :: ConnectionType -> Boolean
    isCurved (Curved _) = true
    isCurved _ = false

  pure $ isCurved conn12 && isCurved conn21

-- | ConnectionType の Show
test_connection_show :: Effect Boolean
test_connection_show = do
  let
    flat = Flat
    curved = Curved "test reason"
    critical = Critical "security issue"

  pure $
    show flat == "Flat" &&
    show curved == "(Curved \"test reason\")" &&
    show critical == "(Critical \"security issue\")"

-- ============================================================
-- ContractTransition テスト
-- ============================================================

-- | ContractTransition の等値性
test_contract_transition_equality :: Effect Boolean
test_contract_transition_equality = do
  pure $
    PreserveOldLaw == PreserveOldLaw &&
    MigrateToNewLaw == MigrateToNewLaw &&
    CaseByCase == CaseByCase &&
    PreserveOldLaw /= MigrateToNewLaw

-- | ContractTransition の Show
test_contract_transition_show :: Effect Boolean
test_contract_transition_show = do
  pure $
    show PreserveOldLaw == "PreserveOldLaw" &&
    show MigrateToNewLaw == "MigrateToNewLaw" &&
    show CaseByCase == "CaseByCase"

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema Nomos Test ==="
  log ""

  log "--- NomosVersion ---"

  log "NomosVersion equality"
  r1 <- test_version_equality
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log "NomosVersion ordering"
  r2 <- test_version_ordering
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log "NomosVersion show"
  r3 <- test_version_show
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- World ---"

  log "mkWorld creates World"
  r4 <- test_mkWorld
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log "World field access"
  r5 <- test_world_fields
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- IntentContext ---"

  log "mkIntentContext creates context"
  r6 <- test_mkIntentContext
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Duration ---"

  log "mkDuration creates duration"
  r7 <- test_mkDuration
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log "Duration equality"
  r8 <- test_duration_equality
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log "Duration ordering"
  r9 <- test_duration_ordering
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Connection verification ---"

  log "Same version = Flat"
  r10 <- test_connection_flat
  log $ "  Result: " <> if r10 then "✓ PASS" else "✗ FAIL"

  log "Different version = Curved"
  r11 <- test_connection_curved
  log $ "  Result: " <> if r11 then "✓ PASS" else "✗ FAIL"

  log "Connection type consistency"
  r12 <- test_connection_type_consistency
  log $ "  Result: " <> if r12 then "✓ PASS" else "✗ FAIL"

  log "ConnectionType show"
  r13 <- test_connection_show
  log $ "  Result: " <> if r13 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ContractTransition ---"

  log "ContractTransition equality"
  r14 <- test_contract_transition_equality
  log $ "  Result: " <> if r14 then "✓ PASS" else "✗ FAIL"

  log "ContractTransition show"
  r15 <- test_contract_transition_show
  log $ "  Result: " <> if r15 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = and [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15]
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
