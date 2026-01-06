-- | Noema Intent: Freer Monad
-- |
-- | 意志（Intent）を Freer Monad として定式化する。
-- |
-- | 圏論的構造：
-- | - Intent ⊣ Cognition 随伴の左随伴（自由関手）
-- | - Vorzeichnungsschema = Freer f = Free(Coyoneda f)
-- | - Codensity 変換により左結合の非効率を解消
-- |
-- | 哲学的基盤：
-- | > プログラムとは、主体が世界に対して投げかける意志を、
-- | > Vorzeichnungsschema として構造化し、認知（Cognition）による
-- | > 忘却を通じて事実へと崩落させる、対話的運動である。
-- |
-- | > 実行とは忘却である。
module Noema.Intent.Freer
  ( Intent
  , liftIntent
  , foldIntent
  , hoistIntent
  , runIntent
  -- Re-exports from Control.Monad.Free
  , module ReExports
  ) where

import Prelude

import Control.Monad.Free (Free, liftF, foldFree, hoistFree, runFree, runFreeM) as ReExports
import Control.Monad.Free (Free, liftF, foldFree, hoistFree)
import Data.Functor (class Functor)

-- | Intent（意志）
-- |
-- | 操作 f に対する自由モナド。
-- | Arrow Effects の制約により、操作は線形な列（sequence）として設計される。
-- |
-- | 圏論的解釈：
-- | Intent f a ≃ Free (Coyoneda f) a
-- | ただし、PureScript の Free は既に Coyoneda 最適化を含む。
type Intent f = Free f

-- | 操作を Intent に持ち上げる
-- |
-- | 圏論的解釈：
-- | η : f a → Intent f a（単位射）
liftIntent :: forall f a. Functor f => f a -> Intent f a
liftIntent = liftF

-- | Intent を解釈する
-- |
-- | 自然変換 f ~> m を用いて Intent f a を m a に変換する。
-- |
-- | 圏論的解釈：
-- | Cognition（忘却）の実装。
-- | Handler は A-algebra homomorphism として機能する。
-- |
-- | > 実行とは忘却である。
foldIntent :: forall f m a. Monad m => (f ~> m) -> Intent f a -> m a
foldIntent = foldFree

-- | Intent の基底関手を変換する
-- |
-- | 自然変換 f ~> g を用いて Intent f を Intent g に変換する。
hoistIntent :: forall f g. Functor g => (f ~> g) -> Intent f ~> Intent g
hoistIntent = hoistFree

-- | Intent を実行する
-- |
-- | Aff などの具体的なモナドで Intent を解釈する。
-- | これは Cognition（認知による忘却）の具体化。
runIntent :: forall f m a. Monad m => (f ~> m) -> Intent f a -> m a
runIntent = foldFree
