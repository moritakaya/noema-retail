-- | Noema Arrow Laws Test - InventoryF
-- |
-- | 実際の InventoryF 語彙を使った Arrow 法則テスト。
-- | Mock Handler を使用して純粋にテスト。
module Test.Laws.ArrowInventory where

import Prelude

import Control.Category (identity, (>>>))
import Control.Arrow (arr, first, (&&&))
import Data.Tuple (Tuple(..), fst)
import Data.Identity (Identity(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Console (log)

import Noema.Vorzeichnung.Intent (Intent', runIntent)
import Noema.Core.Locus (ThingId(..), SubjectId, Quantity(..), QuantityDelta(..), mkSubjectId)
import Noema.Presheaf.Channel (Channel(..))
import Noema.Vorzeichnung.Vocabulary.InventoryF
  ( InventoryF(..)
  , InventoryIntent
  , StockInfo
  , SyncResult(..)
  , getStock
  , adjustStock
  )

-- ============================================================
-- Mock Handler
-- ============================================================

-- | Mock Handler（純粋版 - Identity）
-- |
-- | 状態を持たない簡易版。ハードコードされたデータを返す。
-- |
-- | 注: LocationId は SubjectId に統合された。
mockHandlerPure :: InventoryF ~> Identity
mockHandlerPure = case _ of
  GetStock (ThingId tid) sid k ->
    let info = case tid of
          "SKU-001" ->
            { thingId: ThingId "SKU-001"
            , subjectId: sid
            , quantity: Quantity 100
            , reserved: Quantity 10
            , available: Quantity 90
            }
          "SKU-002" ->
            { thingId: ThingId "SKU-002"
            , subjectId: sid
            , quantity: Quantity 50
            , reserved: Quantity 0
            , available: Quantity 50
            }
          _ -> defaultStock tid sid
    in Identity (k info)

  SetStock _ _ _ next ->
    Identity next

  AdjustStock (ThingId tid) _sid (QuantityDelta delta) k ->
    -- 簡易実装: 現在の数量に delta を加算
    let baseQty = case tid of
          "SKU-001" -> 100
          "SKU-002" -> 50
          _ -> 0
        newQty = Quantity (baseQty + delta)
    in Identity (k newQty)

  ReserveStock _ _ _ k ->
    Identity (k true)

  ReleaseReservation _ _ _ next ->
    Identity next

  SyncToChannel channel _ qty k ->
    Identity (k (SyncSuccess { channel, quantity: qty }))

  SyncFromChannel _channel (ThingId tid) k ->
    Identity (k (defaultStock tid (mkSubjectId "default")))

-- | デフォルト在庫
defaultStock :: String -> SubjectId -> StockInfo
defaultStock tid sid =
  { thingId: ThingId tid
  , subjectId: sid
  , quantity: Quantity 0
  , reserved: Quantity 0
  , available: Quantity 0
  }

-- | Intent を純粋に実行
runInventoryTest :: forall a b. InventoryIntent a b -> a -> b
runInventoryTest intent input = unwrap (runIntent mockHandlerPure intent input)

-- ============================================================
-- Arrow 法則テスト（InventoryF）
-- ============================================================

-- | 法則 1: arr id = id
testLaw1 :: Effect Boolean
testLaw1 = do
  let
    tid = ThingId "SKU-001"
    sid = mkSubjectId "LOC-001"

    -- getStock >>> arr id
    left :: InventoryIntent Unit StockInfo
    left = getStock tid sid >>> arr identity

    -- getStock >>> id
    right :: InventoryIntent Unit StockInfo
    right = getStock tid sid >>> identity

    resultL = runInventoryTest left unit
    resultR = runInventoryTest right unit

  pure (resultL.quantity == resultR.quantity)

-- | 法則 2: arr (g <<< f) = arr g <<< arr f
testLaw2 :: Effect Boolean
testLaw2 = do
  let
    tid = ThingId "SKU-001"
    sid = mkSubjectId "LOC-001"

    f :: StockInfo -> Quantity
    f info = info.quantity

    g :: Quantity -> Int
    g (Quantity q) = q * 2

    -- getStock >>> arr (g <<< f)
    left :: InventoryIntent Unit Int
    left = getStock tid sid >>> arr (g <<< f)

    -- getStock >>> arr f >>> arr g
    right :: InventoryIntent Unit Int
    right = getStock tid sid >>> arr f >>> arr g

    resultL = runInventoryTest left unit
    resultR = runInventoryTest right unit

  pure (resultL == resultR)

-- | 法則 4: first (f >>> g) = first f >>> first g
testLaw4 :: Effect Boolean
testLaw4 = do
  let
    tid = ThingId "SKU-001"
    sid = mkSubjectId "LOC-001"

    f :: InventoryIntent Unit StockInfo
    f = getStock tid sid

    g :: InventoryIntent StockInfo Quantity
    g = arr _.quantity

    -- first (f >>> g)
    left :: InventoryIntent (Tuple Unit String) (Tuple Quantity String)
    left = first (f >>> g)

    -- first f >>> first g
    right :: InventoryIntent (Tuple Unit String) (Tuple Quantity String)
    right = first f >>> first g

    input = Tuple unit "context"

    resultL = runInventoryTest left input
    resultR = runInventoryTest right input

  pure (resultL == resultR)

-- | 法則 5: first f >>> arr fst = arr fst >>> f
testLaw5 :: Effect Boolean
testLaw5 = do
  let
    tid = ThingId "SKU-001"
    sid = mkSubjectId "LOC-001"

    f :: InventoryIntent Unit StockInfo
    f = getStock tid sid

    -- first f >>> arr fst
    left :: InventoryIntent (Tuple Unit String) StockInfo
    left = first f >>> arr fst

    -- arr fst >>> f
    right :: InventoryIntent (Tuple Unit String) StockInfo
    right = arr fst >>> f

    input = Tuple unit "ignored"

    resultL = runInventoryTest left input
    resultR = runInventoryTest right input

  pure (resultL.quantity == resultR.quantity)

-- | &&& の検証: f &&& g で両方の結果を得る
testFanout :: Effect Boolean
testFanout = do
  let
    tid1 = ThingId "SKU-001"
    tid2 = ThingId "SKU-002"
    sid = mkSubjectId "LOC-001"

    f :: InventoryIntent Unit StockInfo
    f = getStock tid1 sid

    g :: InventoryIntent Unit StockInfo
    g = getStock tid2 sid

    -- f &&& g
    combined :: InventoryIntent Unit (Tuple StockInfo StockInfo)
    combined = f &&& g

    result = runInventoryTest combined unit

    (Tuple info1 info2) = result

  -- SKU-001 は 100, SKU-002 は 50
  pure (info1.quantity == Quantity 100 && info2.quantity == Quantity 50)

-- ============================================================
-- 実用的なパターンテスト
-- ============================================================

-- | 在庫取得 → 数量抽出 のパイプライン
testPipeline :: Effect Boolean
testPipeline = do
  let
    tid = ThingId "SKU-001"
    sid = mkSubjectId "LOC-001"

    -- 在庫取得 → 数量抽出 → 2倍
    pipeline :: InventoryIntent Unit Int
    pipeline =
      getStock tid sid
      >>> arr _.quantity
      >>> arr (\(Quantity q) -> q * 2)

    result = runInventoryTest pipeline unit

  -- 100 * 2 = 200
  pure (result == 200)

-- | 複数在庫の並列取得
testParallel :: Effect Boolean
testParallel = do
  let
    tid = ThingId "SKU-001"
    sid = mkSubjectId "LOC-001"

    -- 在庫と予約を両方取得
    getQuantities :: InventoryIntent Unit (Tuple Quantity Quantity)
    getQuantities =
      getStock tid sid
      >>> (arr _.quantity &&& arr _.reserved)

    (Tuple qty reserved) = runInventoryTest getQuantities unit

  -- quantity = 100, reserved = 10
  pure (qty == Quantity 100 && reserved == Quantity 10)

-- ============================================================
-- テスト実行
-- ============================================================

-- | InventoryF テストを実行
runInventoryTests :: Effect Unit
runInventoryTests = do
  log "=== InventoryF Arrow Laws Test ==="
  log ""
  
  log "Law 1 (with effect): arr id = id"
  r1 <- testLaw1
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"
  
  log "Law 2 (with effect): arr (g <<< f) = arr g <<< arr f"
  r2 <- testLaw2
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"
  
  log "Law 4 (with effect): first (f >>> g) = first f >>> first g"
  r4 <- testLaw4
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"
  
  log "Law 5 (with effect): first f >>> arr fst = arr fst >>> f"
  r5 <- testLaw5
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"
  
  log ""
  log "--- Practical Patterns ---"
  
  log "Fanout (f &&& g)"
  rf <- testFanout
  log $ "  Result: " <> if rf then "✓ PASS" else "✗ FAIL"
  
  log "Pipeline (getStock >>> arr _.quantity >>> arr (*2))"
  rp <- testPipeline
  log $ "  Result: " <> if rp then "✓ PASS" else "✗ FAIL"
  
  log "Parallel (arr _.quantity &&& arr _.reserved)"
  rr <- testParallel
  log $ "  Result: " <> if rr then "✓ PASS" else "✗ FAIL"
  
  log ""
  let allPassed = r1 && r2 && r4 && r5 && rf && rp && rr
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
