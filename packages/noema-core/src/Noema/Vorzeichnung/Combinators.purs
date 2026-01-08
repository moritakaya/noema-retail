-- | Noema Arrow Combinators
-- |
-- | Arrow ベースの Intent を組み立てるためのコンビネータ。
-- |
-- | ## Monad (do記法) vs Arrow (>>>記法) の比較
-- |
-- | ```purescript
-- | -- ❌ Monad スタイル（Noema では禁止）
-- | monadicIntent = do
-- |   x <- getStock
-- |   if x > 0 then adjustStock (-1) else reserve 1  -- 分岐！
-- |   pure x
-- |
-- | -- ✅ Arrow スタイル（Noema の正しい書き方）
-- | arrowIntent = 
-- |   getStock 
-- |   >>> arr (\x -> (x, x - 1)) 
-- |   >>> second setStock
-- |   >>> arr fst
-- | ```
-- |
-- | Arrow では構造が静的に確定するため、
-- | Handler の合成が容易になり、最適化の余地が生まれる。
module Noema.Vorzeichnung.Combinators
  ( -- * Basic combinators
    eff_
  , constant
  , ignore
    -- * Tuple manipulation
  , dup
  , swap
  , assocL
  , assocR
    -- * Conditional (without branching!)
  , guard
  , assert
    -- * Sequencing
  , andThen
  , (>>>!)
    -- * Parallel
  , both
  , fanout
  ) where

import Prelude

import Control.Category (identity, (>>>))
import Control.Arrow (class Arrow, arr, first, second, (***), (&&&))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))

import Noema.Vorzeichnung.Intent (Intent, liftEffect)

-- ============================================================
-- Basic combinators
-- ============================================================

-- | 効果を持ち上げる（入力を渡す）
-- |
-- | Note: この関数は Arrow (ArrowApply なし) では実装不可能。
-- | 入力に基づいてエフェクトを動的に選択することになり、
-- | Arrow の線形構造（分岐禁止）を破るため。
-- |
-- | ArrowApply が必要: app :: a (a b c, b) c
-- |
-- | ```purescript
-- | -- 代わりに liftEffect と arr を組み合わせる
-- | -- eff GetStock :: Intent InventoryF ProductId Quantity
-- | ```
-- |
-- | eff :: forall f a b. (a -> f b) -> Intent f a b
-- | eff f = arr f >>> liftEffect'
-- |   where
-- |     liftEffect' :: Intent f (f b) b
-- |     liftEffect' = undefined -- ArrowApply が必要

-- | 効果を持ち上げる（入力を無視）
-- |
-- | ```purescript
-- | eff_ (Log "hello") :: Intent LogF a Unit
-- | ```
eff_ :: forall f a b. f b -> Intent f a b
eff_ = liftEffect

-- | 定数を返す
-- |
-- | ```purescript
-- | constant 42 :: Intent f a Int
-- | ```
constant :: forall f a b. b -> Intent f a b
constant b = arr (const b)

-- | 入力を無視して Unit を返す
-- |
-- | ```purescript
-- | ignore :: Intent f a Unit
-- | ```
ignore :: forall f a. Intent f a Unit
ignore = arr (const unit)

-- ============================================================
-- Tuple manipulation
-- ============================================================

-- | 入力を複製
-- |
-- | ```purescript
-- | dup :: Intent f a (Tuple a a)
-- | dup >>> (processA *** processB)
-- | ```
dup :: forall f a. Intent f a (Tuple a a)
dup = arr (\a -> Tuple a a)

-- | Tuple の要素を交換
swap :: forall f a b. Intent f (Tuple a b) (Tuple b a)
swap = arr (\(Tuple a b) -> Tuple b a)

-- | 左結合
assocL :: forall f a b c. Intent f (Tuple a (Tuple b c)) (Tuple (Tuple a b) c)
assocL = arr (\(Tuple a (Tuple b c)) -> Tuple (Tuple a b) c)

-- | 右結合
assocR :: forall f a b c. Intent f (Tuple (Tuple a b) c) (Tuple a (Tuple b c))
assocR = arr (\(Tuple (Tuple a b) c) -> Tuple a (Tuple b c))

-- ============================================================
-- Conditional (without branching!)
-- ============================================================

-- | 条件ガード（分岐ではない！）
-- |
-- | 条件が false の場合、Nothing を返す。
-- | これは「分岐」ではなく「フィルタリング」。
-- |
-- | ```purescript
-- | checkStock = 
-- |   getStock
-- |   >>> guard (_ > 0)  -- 在庫がなければ Nothing
-- |   >>> arr (map (_ - 1))
-- | ```
-- |
-- | 重要: guard は ArrowChoice を使わない。
-- | 結果の型が Maybe になるだけで、経路は分岐しない。
guard :: forall f a. (a -> Boolean) -> Intent f a (Maybe a)
guard pred = arr (\a -> if pred a then Just a else Nothing)

-- | アサーション（条件が false なら失敗値を埋め込む）
-- |
-- | ```purescript
-- | assert (_ > 0) "Stock must be positive"
-- | ```
assert :: forall f a e. (a -> Boolean) -> e -> Intent f a (Either e a)
assert pred err = arr (\a -> if pred a then Right a else Left err)

-- ============================================================
-- Sequencing
-- ============================================================

-- | 明示的な列結合（>>> の別名）
andThen :: forall f a b c. Intent f a b -> Intent f b c -> Intent f a c
andThen = (>>>)

-- | 中置演算子（>>> の別名、視認性向上）
infixr 1 andThen as >>>!

-- ============================================================
-- Parallel
-- ============================================================

-- | 両方の経路を実行
-- |
-- | ```purescript
-- | both getStock getPrice :: Intent f ProductId (Tuple Quantity Price)
-- | ```
both :: forall f a b c. Intent f a b -> Intent f a c -> Intent f a (Tuple b c)
both f g = dup >>> (f *** g)

-- | 入力を複製して両方の経路に流す（&&& の別名）
fanout :: forall f a b c. Intent f a b -> Intent f a c -> Intent f a (Tuple b c)
fanout = (&&&)

-- ============================================================
-- Why no branching?
-- ============================================================

-- | ❌ 以下は Noema では実装しない
-- |
-- | ```purescript
-- | -- ArrowChoice の left/right は存在しない
-- | branch :: Intent f (Either a b) c  -- 不可能！
-- | 
-- | -- 条件分岐で異なる経路を選ぶことはできない
-- | ifThenElse :: Intent f a b -> Intent f a b -> Intent f (Tuple Bool a) b  -- 不可能！
-- | ```
-- |
-- | これは制限ではなく、設計上の選択である。
-- |
-- | ## 理由
-- |
-- | 1. **静的解析可能性**: 構造が静的に確定するため、
-- |    Handler の合成や最適化が容易になる。
-- |
-- | 2. **哲学的整合性**: 「意志」は実行前に完全に記述される。
-- |    実行時の分岐は「反応」であり、Noema の対象外。
-- |
-- | 3. **分散システムでの利点**: 静的な構造は
-- |    ネットワーク越しに伝達・検証しやすい。
-- |
-- | ## 分岐が必要な場合
-- |
-- | 分岐はセマンティクスレベル（Handler）で実装する:
-- |
-- | ```purescript
-- | -- 語彙に条件付き操作を追加
-- | data InventoryF a
-- |   = ...
-- |   | ConditionalAdjust ProductId Quantity (Boolean -> a)
-- |
-- | -- Handler で分岐を実装
-- | handleInventory :: InventoryF ~> Aff
-- | handleInventory (ConditionalAdjust pid qty k) = do
-- |   current <- getStock pid
-- |   if current >= qty
-- |     then do
-- |       adjustStock pid (-qty)
-- |       pure (k true)
-- |     else pure (k false)
-- | ```
-- |
-- | これにより、分岐のセマンティクスは Handler に隠蔽され、
-- | Intent は純粋な「意志の列」として保たれる。
