-- | Noema Combinators Test
-- |
-- | Combinators モジュールの関数をテストする。
-- |
-- | ## テスト対象
-- |
-- | - eff_, constant, ignore
-- | - dup, swap, assocL, assocR
-- | - guard, assert
-- | - andThen, both, fanout
module Test.Combinators where

import Prelude

import Control.Arrow (arr, (&&&), (***))
import Data.Foldable (and)
import Data.Tuple (Tuple(..))
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Console (log)

import Noema.Vorzeichnung.Intent (Intent', realizeIntent)
import Noema.Vorzeichnung.Combinators
  ( eff_
  , constant
  , ignore
  , dup
  , swap
  , assocL
  , assocR
  , guard
  , assert
  , andThen
  , both
  , fanout
  )

-- ============================================================
-- テスト用の語彙と Interpretation
-- ============================================================

-- | テスト用の単純な語彙
data TestF a
  = Pure a
  | GetValue (Int -> a)
  | PutValue Int a

derive instance functorTestF :: Functor TestF

-- | TestF の Identity Interpretation
testInterpretation :: TestF ~> Identity
testInterpretation = case _ of
  Pure a -> Identity a
  GetValue k -> Identity (k 42)  -- 固定値を返す
  PutValue _ a -> Identity a     -- 値を無視

-- | Intent を純粋に実行
runTest :: forall a b. Intent' TestF a b -> a -> b
runTest intent input = unwrap (realizeIntent testInterpretation intent input)

-- ============================================================
-- Basic combinators tests
-- ============================================================

-- | eff_ は効果を持ち上げる（入力を無視）
test_eff :: Effect Boolean
test_eff = do
  let
    intent :: Intent' TestF String Int
    intent = eff_ (GetValue identity)

    result = runTest intent "ignored input"

  pure (result == 42)

-- | constant は定数を返す
test_constant :: Effect Boolean
test_constant = do
  let
    intent :: Intent' TestF Int String
    intent = constant "hello"

    results =
      [ runTest intent 0 == "hello"
      , runTest intent 999 == "hello"
      , runTest intent (-1) == "hello"
      ]

  pure (and results)

-- | ignore は Unit を返す
test_ignore :: Effect Boolean
test_ignore = do
  let
    intent :: Intent' TestF String Unit
    intent = ignore

    results =
      [ runTest intent "anything" == unit
      , runTest intent "" == unit
      ]

  pure (and results)

-- ============================================================
-- Tuple manipulation tests
-- ============================================================

-- | dup は入力を複製
test_dup :: Effect Boolean
test_dup = do
  let
    intent :: Intent' TestF Int (Tuple Int Int)
    intent = dup

    results =
      [ runTest intent 5 == Tuple 5 5
      , runTest intent 0 == Tuple 0 0
      , runTest intent (-3) == Tuple (-3) (-3)
      ]

  pure (and results)

-- | swap は Tuple の要素を交換
test_swap :: Effect Boolean
test_swap = do
  let
    intent :: Intent' TestF (Tuple Int String) (Tuple String Int)
    intent = swap

    results =
      [ runTest intent (Tuple 1 "a") == Tuple "a" 1
      , runTest intent (Tuple 0 "") == Tuple "" 0
      ]

  pure (and results)

-- | assocL と assocR は逆操作
test_assoc :: Effect Boolean
test_assoc = do
  let
    -- assocR >>> assocL = identity
    roundTrip :: Intent' TestF (Tuple (Tuple Int String) Boolean) (Tuple (Tuple Int String) Boolean)
    roundTrip = assocR >>> assocL

    input = Tuple (Tuple 1 "a") true
    result = runTest roundTrip input

    -- assocL >>> assocR = identity
    roundTrip2 :: Intent' TestF (Tuple Int (Tuple String Boolean)) (Tuple Int (Tuple String Boolean))
    roundTrip2 = assocL >>> assocR

    input2 = Tuple 1 (Tuple "a" true)
    result2 = runTest roundTrip2 input2

  pure (result == input && result2 == input2)

-- | assocL の正しい変換
test_assocL :: Effect Boolean
test_assocL = do
  let
    intent :: Intent' TestF (Tuple Int (Tuple String Boolean)) (Tuple (Tuple Int String) Boolean)
    intent = assocL

    input = Tuple 1 (Tuple "a" true)
    expected = Tuple (Tuple 1 "a") true

  pure (runTest intent input == expected)

-- | assocR の正しい変換
test_assocR :: Effect Boolean
test_assocR = do
  let
    intent :: Intent' TestF (Tuple (Tuple Int String) Boolean) (Tuple Int (Tuple String Boolean))
    intent = assocR

    input = Tuple (Tuple 1 "a") true
    expected = Tuple 1 (Tuple "a" true)

  pure (runTest intent input == expected)

-- ============================================================
-- Conditional tests (without branching!)
-- ============================================================

-- | guard は条件に基づいて Maybe を返す
test_guard :: Effect Boolean
test_guard = do
  let
    intent :: Intent' TestF Int (Maybe Int)
    intent = guard (_ > 0)

    results =
      [ runTest intent 5 == Just 5
      , runTest intent 1 == Just 1
      , runTest intent 0 == Nothing
      , runTest intent (-1) == Nothing
      ]

  pure (and results)

-- | assert は条件に基づいて Either を返す
test_assert :: Effect Boolean
test_assert = do
  let
    intent :: Intent' TestF Int (Either String Int)
    intent = assert (_ > 0) "must be positive"

    results =
      [ runTest intent 5 == Right 5
      , runTest intent 0 == Left "must be positive"
      , runTest intent (-1) == Left "must be positive"
      ]

  pure (and results)

-- ============================================================
-- Sequencing tests
-- ============================================================

-- | andThen は >>> と等価
test_andThen :: Effect Boolean
test_andThen = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 1)

    g :: Intent' TestF Int Int
    g = arr (_ * 2)

    -- andThen
    left :: Intent' TestF Int Int
    left = f `andThen` g

    -- >>>
    right :: Intent' TestF Int Int
    right = f >>> g

    inputs = [0, 1, 5, -3]
    results = map (\i -> runTest left i == runTest right i) inputs

  pure (and results)

-- ============================================================
-- Parallel tests
-- ============================================================

-- | both は入力を複製して両方の経路に流す
test_both :: Effect Boolean
test_both = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 1)

    g :: Intent' TestF Int String
    g = arr show

    intent :: Intent' TestF Int (Tuple Int String)
    intent = both f g

    results =
      [ runTest intent 5 == Tuple 6 "5"
      , runTest intent 0 == Tuple 1 "0"
      ]

  pure (and results)

-- | fanout は &&& と等価
test_fanout :: Effect Boolean
test_fanout = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 1)

    g :: Intent' TestF Int Int
    g = arr (_ * 2)

    -- fanout
    left :: Intent' TestF Int (Tuple Int Int)
    left = fanout f g

    -- &&&
    right :: Intent' TestF Int (Tuple Int Int)
    right = f &&& g

    inputs = [0, 1, 5, -3]
    results = map (\i -> runTest left i == runTest right i) inputs

  pure (and results)

-- | both f g = dup >>> (f *** g) の検証
test_both_definition :: Effect Boolean
test_both_definition = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 1)

    g :: Intent' TestF Int String
    g = arr show

    -- both f g
    left :: Intent' TestF Int (Tuple Int String)
    left = both f g

    -- dup >>> (f *** g)
    right :: Intent' TestF Int (Tuple Int String)
    right = dup >>> (f *** g)

    inputs = [0, 1, 5, -3]
    results = map (\i -> runTest left i == runTest right i) inputs

  pure (and results)

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema Combinators Test ==="
  log ""

  log "--- Basic combinators ---"

  log "eff_: lifts effect (ignores input)"
  r1 <- test_eff
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log "constant: returns constant value"
  r2 <- test_constant
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log "ignore: returns Unit"
  r3 <- test_ignore
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Tuple manipulation ---"

  log "dup: duplicates input"
  r4 <- test_dup
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log "swap: swaps tuple elements"
  r5 <- test_swap
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log "assocL: left association"
  r6 <- test_assocL
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log "assocR: right association"
  r7 <- test_assocR
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log "assoc roundtrip: assocL <<< assocR = identity"
  r8 <- test_assoc
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Conditional (no branching) ---"

  log "guard: filters with Maybe"
  r9 <- test_guard
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log "assert: validates with Either"
  r10 <- test_assert
  log $ "  Result: " <> if r10 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Sequencing ---"

  log "andThen: equivalent to >>>"
  r11 <- test_andThen
  log $ "  Result: " <> if r11 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Parallel ---"

  log "both: duplicates and applies both"
  r12 <- test_both
  log $ "  Result: " <> if r12 then "✓ PASS" else "✗ FAIL"

  log "fanout: equivalent to &&&"
  r13 <- test_fanout
  log $ "  Result: " <> if r13 then "✓ PASS" else "✗ FAIL"

  log "both definition: both f g = dup >>> (f *** g)"
  r14 <- test_both_definition
  log $ "  Result: " <> if r14 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = r1 && r2 && r3 && r4 && r5 && r6 && r7 && r8 && r9 && r10 && r11 && r12 && r13 && r14
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
