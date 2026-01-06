-- | Noema Intent: Freer Arrow
-- |
-- | 意志（Intent）を Freer Arrow として定式化する。
-- |
-- | ## Arrow Effects の核心
-- |
-- | > 効果は「列」として構成される。
-- | > 出力に基づく条件分岐で後続エフェクトを選択しない。
-- |
-- | これを型レベルで強制するため、ArrowChoice を実装しない。
-- |
-- | ## 圏論的構造
-- |
-- | Arrow は以下の構造を持つ:
-- | - Category: 恒等射 id と合成 >>>
-- | - Arrow: arr による純粋関数の持ち上げ、first による強度
-- |
-- | Monad との決定的な違い:
-- | - Monad: 前の結果を見て「どの効果を実行するか」を選べる（動的）
-- | - Arrow: 構造が静的に確定している（静的）
-- |
-- | ## 哲学的基盤
-- |
-- | > 意図は実行前に完全に記述される。
-- | > 実行時の分岐は「意志」ではなく「反応」である。
-- | > Noema は意志の構造を記述する。
module Noema.Vorzeichnung.Freer
  ( Intent
  , IntentF(..)
  , mkIntent
  , liftEffect
  , runIntent
  , hoistIntent
  -- Arrow re-exports
  , module Control.Category
  , module Control.Arrow
  ) where

import Prelude

import Control.Category (class Category, identity, compose, (<<<), (>>>))
import Control.Arrow (class Arrow, arr, first, second, (***), (&&&))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Exists (Exists, mkExists, runExists)
import Effect.Aff (Aff)
import Control.Monad.Rec.Class (class MonadRec, tailRecM, Step(..))

-- | Intent: 入力 a から出力 b への意志の経路
-- |
-- | Arrow として設計され、ArrowChoice を持たない。
-- | これにより「前の結果を見て分岐」が型レベルで禁止される。
-- |
-- | 圏論的には:
-- |   Intent f : Hask → Hask (自己関手)
-- |   ただし ArrowChoice を欠くため、coproduct を保存しない
newtype Intent f a b = Intent (IntentF f a b)

-- | Intent の内部表現
-- |
-- | 静的な構造として効果の「列」を表現する。
-- | GADT がないため、存在型を使用。
data IntentF f a b
  = Arr (a -> b)
    -- ^ 純粋関数の持ち上げ
  | Eff (Exists (EffF f a b))
    -- ^ 効果の実行
  | Seq (Exists (SeqF f a b))
    -- ^ 列の合成
  | Par (Exists (ParF f a b))
    -- ^ 並列合成（first/second）

-- | 効果ノード
-- |
-- | f x を実行し、結果 x を変換して b を得る
newtype EffF f a b x = EffF
  { effect :: f x
  , post :: x -> b
  }

-- | 列合成ノード
-- |
-- | a → x → b の経路
newtype SeqF f a b x = SeqF
  { first :: Intent f a x
  , second :: Intent f x b
  }

-- | 並列合成ノード（first 用）
-- |
-- | (a, c) → (b, c) の経路
newtype ParF f a b c = ParF
  { inner :: Intent f a b
  }

-- ============================================================
-- Category instance
-- ============================================================

instance categoryIntent :: Category (Intent f) where
  identity = Intent (Arr identity)
  
  compose (Intent g) (Intent f) = Intent (Seq (mkExists (SeqF { first: Intent f, second: Intent g })))

-- ============================================================
-- Arrow instance
-- ============================================================

instance arrowIntent :: Arrow (Intent f) where
  arr f = Intent (Arr f)
  
  first (Intent f) = Intent (Par (mkExists (ParF { inner: Intent f })))

-- ============================================================
-- ArrowChoice は意図的に実装しない！
-- ============================================================
-- 
-- instance arrowChoiceIntent :: ArrowChoice (Intent f) where
--   left = ...   -- ← これを実装しないことで分岐を禁止
--   right = ...
--
-- コンパイルエラー例:
--   left someIntent  -- Error: No instance for ArrowChoice (Intent f)
--

-- ============================================================
-- Smart constructors
-- ============================================================

-- | Intent を構築
mkIntent :: forall f a b. (a -> b) -> Intent f a b
mkIntent = arr

-- | 効果を Intent に持ち上げる
-- |
-- | 入力を無視して効果 f b を実行する。
-- | これは最も基本的な効果の持ち上げ。
liftEffect :: forall f a b. f b -> Intent f a b
liftEffect fb = Intent (Eff (mkExists (EffF { effect: fb, post: identity })))

-- | 効果を持ち上げ、結果を変換する
liftEffectWith :: forall f a b x. f x -> (x -> b) -> Intent f a b
liftEffectWith fx post = Intent (Eff (mkExists (EffF { effect: fx, post: post })))

-- ============================================================
-- Interpretation (Cognition)
-- ============================================================

-- | Intent を実行する（忘却）
-- |
-- | Handler（自然変換 f ~> m）を用いて Intent を解釈する。
-- |
-- | Arrow 準同型性:
-- |   runIntent h (f >>> g) = runIntent h f >>> runIntent h g
-- |   runIntent h (arr f) = arr f
-- |   runIntent h (first f) = first (runIntent h f)
runIntent
  :: forall f m a b
   . MonadRec m
  => (forall x. f x -> m x)  -- ^ Handler
  -> Intent f a b
  -> (a -> m b)
runIntent handler (Intent intent) = case intent of
  Arr f -> 
    pure <<< f
  
  Eff ex -> 
    runExists (\(EffF { effect, post }) -> \_ -> do
      x <- handler effect
      pure (post x)
    ) ex
  
  Seq ex ->
    runExists (\(SeqF { first: f, second: g }) -> \a -> do
      x <- runIntent handler f a
      runIntent handler g x
    ) ex
  
  Par ex ->
    runExists (\(ParF { inner }) -> \(Tuple a c) -> do
      b <- runIntent handler inner a
      pure (Tuple b c)
    ) ex

-- | Intent の基底関手を変換する
hoistIntent
  :: forall f g a b
   . (forall x. f x -> g x)
  -> Intent f a b
  -> Intent g a b
hoistIntent nat (Intent intent) = Intent (hoistIntentF nat intent)

hoistIntentF
  :: forall f g a b
   . (forall x. f x -> g x)
  -> IntentF f a b
  -> IntentF g a b
hoistIntentF nat = case _ of
  Arr f -> 
    Arr f
  
  Eff ex ->
    Eff (runExists (\(EffF { effect, post }) -> 
      mkExists (EffF { effect: nat effect, post: post })
    ) ex)
  
  Seq ex ->
    Seq (runExists (\(SeqF { first: f, second: g }) ->
      mkExists (SeqF 
        { first: hoistIntent nat f
        , second: hoistIntent nat g
        })
    ) ex)
  
  Par ex ->
    Par (runExists (\(ParF { inner }) ->
      mkExists (ParF { inner: hoistIntent nat inner })
    ) ex)
