-- | Noema Factum Test
-- |
-- | Factum（事実）モジュールのテスト。
-- |
-- | ## テスト対象
-- |
-- | - collapse/recognize の対称性
-- | - Functor/Applicative/Monad インスタンス
-- | - MonadRec インスタンス
module Test.Factum where

import Prelude

import Data.Foldable (and)
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref

import Noema.Sedimentation.Factum
  ( Factum
  , collapse
  , recognize
  , liftFactum
  )

-- ============================================================
-- collapse/recognize 対称性テスト
-- ============================================================

-- | recognize >>> collapse = identity
test_recognize_collapse :: Effect Boolean
test_recognize_collapse = do
  let
    original :: Effect Int
    original = pure 42

    -- recognize >>> collapse
    roundTrip :: Effect Int
    roundTrip = collapse (recognize original)

  result <- roundTrip
  pure (result == 42)

-- | collapse >>> recognize = identity (意味論的)
-- |
-- | 注: この等式は参照透過性の意味で成り立つ
test_collapse_recognize :: Effect Boolean
test_collapse_recognize = do
  let
    original :: Factum Int
    original = recognize (pure 42)

    -- collapse >>> recognize
    roundTrip :: Factum Int
    roundTrip = recognize (collapse original)

  result <- collapse roundTrip
  pure (result == 42)

-- ============================================================
-- Functor テスト
-- ============================================================

-- | Functor 恒等則: fmap id = id
test_functor_identity :: Effect Boolean
test_functor_identity = do
  let
    factum :: Factum Int
    factum = recognize (pure 42)

    mapped :: Factum Int
    mapped = map identity factum

  original <- collapse factum
  result <- collapse mapped
  pure (result == original)

-- | Functor 合成則: fmap (g . f) = fmap g . fmap f
test_functor_composition :: Effect Boolean
test_functor_composition = do
  let
    f :: Int -> Int
    f x = x + 1

    g :: Int -> Int
    g x = x * 2

    factum :: Factum Int
    factum = recognize (pure 5)

    -- map (g <<< f)
    left :: Factum Int
    left = map (g <<< f) factum

    -- map g <<< map f
    right :: Factum Int
    right = (map g <<< map f) factum

  l <- collapse left
  r <- collapse right
  pure (l == r)

-- ============================================================
-- Applicative テスト
-- ============================================================

-- | pure x で値を持ち上げる
test_applicative_pure :: Effect Boolean
test_applicative_pure = do
  let
    factum :: Factum String
    factum = pure "hello"

  result <- collapse factum
  pure (result == "hello")

-- | apply で関数適用
test_applicative_apply :: Effect Boolean
test_applicative_apply = do
  let
    factumF :: Factum (Int -> Int)
    factumF = pure (_ + 10)

    factumX :: Factum Int
    factumX = pure 5

    result :: Factum Int
    result = factumF <*> factumX

  r <- collapse result
  pure (r == 15)

-- ============================================================
-- Monad テスト
-- ============================================================

-- | bind でシーケンス
test_monad_bind :: Effect Boolean
test_monad_bind = do
  let
    factum :: Factum Int
    factum = do
      x <- pure 5
      y <- pure 10
      pure (x + y)

  result <- collapse factum
  pure (result == 15)

-- | 左恒等則: pure a >>= f = f a
test_monad_left_identity :: Effect Boolean
test_monad_left_identity = do
  let
    f :: Int -> Factum Int
    f x = pure (x * 2)

    a :: Int
    a = 21

    -- pure a >>= f
    left :: Factum Int
    left = pure a >>= f

    -- f a
    right :: Factum Int
    right = f a

  l <- collapse left
  r <- collapse right
  pure (l == r)

-- | 右恒等則: m >>= pure = m
test_monad_right_identity :: Effect Boolean
test_monad_right_identity = do
  let
    m :: Factum Int
    m = pure 42

    -- m >>= pure
    left :: Factum Int
    left = m >>= pure

  l <- collapse left
  r <- collapse m
  pure (l == r)

-- ============================================================
-- liftFactum テスト
-- ============================================================

-- | liftFactum で Effect を Factum に持ち上げる
test_liftFactum :: Effect Boolean
test_liftFactum = do
  ref <- Ref.new 0

  let
    factum :: Factum Unit
    factum = liftFactum $ Ref.write 42 ref

  _ <- collapse factum
  result <- Ref.read ref
  pure (result == 42)

-- ============================================================
-- 副作用を含むテスト
-- ============================================================

-- | 副作用が正しく実行される
test_side_effects :: Effect Boolean
test_side_effects = do
  ref <- Ref.new ""

  let
    factum :: Factum String
    factum = do
      liftFactum $ Ref.modify_ (_ <> "A") ref
      liftFactum $ Ref.modify_ (_ <> "B") ref
      liftFactum $ Ref.modify_ (_ <> "C") ref
      liftFactum $ Ref.read ref

  result <- collapse factum
  pure (result == "ABC")

-- | 副作用の順序が保持される
test_effect_order :: Effect Boolean
test_effect_order = do
  ref <- Ref.new ([] :: Array Int)

  let
    factum :: Factum (Array Int)
    factum = do
      liftFactum $ Ref.modify_ (_ <> [1]) ref
      liftFactum $ Ref.modify_ (_ <> [2]) ref
      liftFactum $ Ref.modify_ (_ <> [3]) ref
      liftFactum $ Ref.read ref

  result <- collapse factum
  pure (result == [1, 2, 3])

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema Factum Test ==="
  log ""

  log "--- collapse/recognize symmetry ---"

  log "recognize >>> collapse = identity"
  r1 <- test_recognize_collapse
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log "collapse >>> recognize = identity (semantic)"
  r2 <- test_collapse_recognize
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Functor laws ---"

  log "Functor identity: map id = id"
  r3 <- test_functor_identity
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log "Functor composition: map (g <<< f) = map g <<< map f"
  r4 <- test_functor_composition
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Applicative ---"

  log "pure lifts value"
  r5 <- test_applicative_pure
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log "apply applies function"
  r6 <- test_applicative_apply
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Monad laws ---"

  log "bind sequences effects"
  r7 <- test_monad_bind
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log "Left identity: pure a >>= f = f a"
  r8 <- test_monad_left_identity
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log "Right identity: m >>= pure = m"
  r9 <- test_monad_right_identity
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- liftFactum ---"

  log "liftFactum lifts Effect to Factum"
  r10 <- test_liftFactum
  log $ "  Result: " <> if r10 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Side effects ---"

  log "Side effects execute correctly"
  r11 <- test_side_effects
  log $ "  Result: " <> if r11 then "✓ PASS" else "✗ FAIL"

  log "Effect order is preserved"
  r12 <- test_effect_order
  log $ "  Result: " <> if r12 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = and [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
