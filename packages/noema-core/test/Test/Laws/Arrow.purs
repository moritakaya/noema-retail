-- | Noema Arrow Laws Test
-- |
-- | Arrow 法則の検証テスト。
-- | Intent が Arrow として正しく振る舞うことを確認する。
-- |
-- | ## Arrow 法則
-- |
-- | 1. arr id = id
-- | 2. arr (g <<< f) = arr g <<< arr f
-- | 3. first (arr f) = arr (first f)
-- | 4. first (f >>> g) = first f >>> first g
-- | 5. first f >>> arr fst = arr fst >>> f
-- | 6. first f >>> arr (id *** g) = arr (id *** g) >>> first f
-- | 7. first (first f) >>> arr assoc = arr assoc >>> first f
-- |
-- | ## 実行方法
-- |
-- | ```bash
-- | spago test
-- | ```
module Test.Laws.Arrow where

import Prelude

import Control.Category (identity, (>>>), (<<<))
import Control.Arrow (arr, first, second, (***), (&&&))
import Data.Foldable (and)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Identity (Identity(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Console (log)

import Noema.Vorzeichnung.Intent (Intent', runIntent, arrIntent)

-- ============================================================
-- テスト用の純粋な語彙
-- ============================================================

-- | テスト用の単純な語彙
-- |
-- | 副作用なし、純粋な計算のみ
data TestF a
  = Pure a
  | AddOne Int (Int -> a)
  | Double Int (Int -> a)
  | Concat String String (String -> a)

derive instance functorTestF :: Functor TestF

-- | TestF の Identity Handler
-- |
-- | 純粋な計算として実行
testHandler :: TestF ~> Identity
testHandler = case _ of
  Pure a -> Identity a
  AddOne n k -> Identity (k (n + 1))
  Double n k -> Identity (k (n * 2))
  Concat s1 s2 k -> Identity (k (s1 <> s2))

-- | Intent を純粋に実行
runTest :: forall a b. Intent' TestF a b -> a -> b
runTest intent input = unwrap (runIntent testHandler intent input)

-- ============================================================
-- Arrow 法則テスト
-- ============================================================

-- | 法則 1: arr id = id
-- |
-- | 恒等関数を持ち上げると恒等射になる
law1_arrId :: Effect Boolean
law1_arrId = do
  let
    -- arr id
    left :: Intent' TestF Int Int
    left = arr identity
    
    -- id
    right :: Intent' TestF Int Int
    right = identity
    
    -- テスト入力
    inputs = [0, 1, 42, -10, 999]
    
    -- 両辺を比較
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- | 法則 2: arr (g <<< f) = arr g <<< arr f
-- |
-- | 関数合成を保存する
law2_arrCompose :: Effect Boolean
law2_arrCompose = do
  let
    f :: Int -> Int
    f x = x + 1
    
    g :: Int -> Int
    g x = x * 2
    
    -- arr (g <<< f)
    left :: Intent' TestF Int Int
    left = arr (g <<< f)
    
    -- arr g <<< arr f
    right :: Intent' TestF Int Int
    right = arr g <<< arr f
    
    inputs = [0, 1, 5, -3, 100]
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- | 法則 3: first (arr f) = arr (first f)
-- |
-- | first と arr の交換則
law3_firstArr :: Effect Boolean
law3_firstArr = do
  let
    f :: Int -> Int
    f x = x * 3
    
    -- first (arr f)
    left :: Intent' TestF (Tuple Int String) (Tuple Int String)
    left = first (arr f)
    
    -- arr (first f)
    -- Note: first for functions: first f (a, b) = (f a, b)
    firstF :: forall a b c. (a -> c) -> Tuple a b -> Tuple c b
    firstF fn (Tuple a b) = Tuple (fn a) b
    
    right :: Intent' TestF (Tuple Int String) (Tuple Int String)
    right = arr (firstF f)
    
    inputs = 
      [ Tuple 1 "a"
      , Tuple 0 "hello"
      , Tuple (-5) "test"
      , Tuple 100 ""
      ]
    
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- | 法則 4: first (f >>> g) = first f >>> first g
-- |
-- | first と合成の分配則
law4_firstCompose :: Effect Boolean
law4_firstCompose = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 1)
    
    g :: Intent' TestF Int Int
    g = arr (_ * 2)
    
    -- first (f >>> g)
    left :: Intent' TestF (Tuple Int String) (Tuple Int String)
    left = first (f >>> g)
    
    -- first f >>> first g
    right :: Intent' TestF (Tuple Int String) (Tuple Int String)
    right = first f >>> first g
    
    inputs = 
      [ Tuple 0 "x"
      , Tuple 1 "y"
      , Tuple 10 "z"
      ]
    
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- | 法則 5: first f >>> arr fst = arr fst >>> f
-- |
-- | 投影との関係
law5_firstFst :: Effect Boolean
law5_firstFst = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 10)
    
    -- first f >>> arr fst
    left :: Intent' TestF (Tuple Int String) Int
    left = first f >>> arr fst
    
    -- arr fst >>> f
    right :: Intent' TestF (Tuple Int String) Int
    right = arr fst >>> f
    
    inputs = 
      [ Tuple 0 "a"
      , Tuple 5 "b"
      , Tuple (-3) "c"
      ]
    
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- | 法則 6: first f >>> arr (id *** g) = arr (id *** g) >>> first f
-- |
-- | 交換則（second 要素の変換との独立性）
law6_firstSwap :: Effect Boolean
law6_firstSwap = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ * 2)
    
    g :: String -> String
    g s = s <> "!"
    
    -- id *** g for functions
    idTimesG :: Tuple Int String -> Tuple Int String
    idTimesG (Tuple a b) = Tuple a (g b)
    
    -- first f >>> arr (id *** g)
    left :: Intent' TestF (Tuple Int String) (Tuple Int String)
    left = first f >>> arr idTimesG
    
    -- arr (id *** g) >>> first f
    right :: Intent' TestF (Tuple Int String) (Tuple Int String)
    right = arr idTimesG >>> first f
    
    inputs = 
      [ Tuple 1 "hi"
      , Tuple 0 ""
      , Tuple (-1) "test"
      ]
    
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- | 法則 7: first (first f) >>> arr assoc = arr assoc >>> first f
-- |
-- | 結合則
law7_assoc :: Effect Boolean
law7_assoc = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 1)
    
    -- assoc :: ((a, b), c) -> (a, (b, c))
    assoc :: forall a b c. Tuple (Tuple a b) c -> Tuple a (Tuple b c)
    assoc (Tuple (Tuple a b) c) = Tuple a (Tuple b c)
    
    -- first (first f) >>> arr assoc
    left :: Intent' TestF (Tuple (Tuple Int String) Boolean) (Tuple Int (Tuple String Boolean))
    left = first (first f) >>> arr assoc
    
    -- arr assoc >>> first f
    right :: Intent' TestF (Tuple (Tuple Int String) Boolean) (Tuple Int (Tuple String Boolean))
    right = arr assoc >>> first f
    
    inputs = 
      [ Tuple (Tuple 0 "a") true
      , Tuple (Tuple 5 "b") false
      , Tuple (Tuple (-1) "") true
      ]
    
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- ============================================================
-- 追加テスト: second, ***, &&&
-- ============================================================

-- | second f = arr swap >>> first f >>> arr swap
law_second :: Effect Boolean
law_second = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ * 3)
    
    swap :: forall a b. Tuple a b -> Tuple b a
    swap (Tuple a b) = Tuple b a
    
    -- second f
    left :: Intent' TestF (Tuple String Int) (Tuple String Int)
    left = second f
    
    -- arr swap >>> first f >>> arr swap
    right :: Intent' TestF (Tuple String Int) (Tuple String Int)
    right = arr swap >>> first f >>> arr swap
    
    inputs = 
      [ Tuple "a" 1
      , Tuple "b" 0
      , Tuple "" (-5)
      ]
    
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- | f *** g = first f >>> second g
law_split :: Effect Boolean
law_split = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 1)
    
    g :: Intent' TestF String String
    g = arr (_ <> "!")
    
    -- f *** g
    left :: Intent' TestF (Tuple Int String) (Tuple Int String)
    left = f *** g
    
    -- first f >>> second g
    right :: Intent' TestF (Tuple Int String) (Tuple Int String)
    right = first f >>> second g
    
    inputs = 
      [ Tuple 0 "hi"
      , Tuple 5 ""
      ]
    
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- | f &&& g = arr (\b -> (b, b)) >>> (f *** g)
law_fanout :: Effect Boolean
law_fanout = do
  let
    f :: Intent' TestF Int Int
    f = arr (_ + 1)
    
    g :: Intent' TestF Int Int
    g = arr (_ * 2)
    
    dup :: forall a. a -> Tuple a a
    dup a = Tuple a a
    
    -- f &&& g
    left :: Intent' TestF Int (Tuple Int Int)
    left = f &&& g
    
    -- arr dup >>> (f *** g)
    right :: Intent' TestF Int (Tuple Int Int)
    right = arr dup >>> (f *** g)
    
    inputs = [0, 1, 5, -3]
    
    results = map (\i -> runTest left i == runTest right i) inputs
  
  pure (and results)

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema Arrow Laws Test ==="
  log ""
  
  -- 基本法則
  log "Law 1: arr id = id"
  r1 <- law1_arrId
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"
  
  log "Law 2: arr (g <<< f) = arr g <<< arr f"
  r2 <- law2_arrCompose
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"
  
  log "Law 3: first (arr f) = arr (first f)"
  r3 <- law3_firstArr
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"
  
  log "Law 4: first (f >>> g) = first f >>> first g"
  r4 <- law4_firstCompose
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"
  
  log "Law 5: first f >>> arr fst = arr fst >>> f"
  r5 <- law5_firstFst
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"
  
  log "Law 6: first f >>> arr (id *** g) = arr (id *** g) >>> first f"
  r6 <- law6_firstSwap
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"
  
  log "Law 7: first (first f) >>> arr assoc = arr assoc >>> first f"
  r7 <- law7_assoc
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"
  
  log ""
  log "--- Derived Laws ---"
  
  log "second f = arr swap >>> first f >>> arr swap"
  rs <- law_second
  log $ "  Result: " <> if rs then "✓ PASS" else "✗ FAIL"
  
  log "f *** g = first f >>> second g"
  rp <- law_split
  log $ "  Result: " <> if rp then "✓ PASS" else "✗ FAIL"
  
  log "f &&& g = arr dup >>> (f *** g)"
  rf <- law_fanout
  log $ "  Result: " <> if rf then "✓ PASS" else "✗ FAIL"
  
  log ""
  let allPassed = r1 && r2 && r3 && r4 && r5 && r6 && r7 && rs && rp && rf
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
