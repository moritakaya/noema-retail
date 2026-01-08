-- | Control.Arrow for PureScript
-- |
-- | Arrow 型クラスとその基本的な操作を定義する。
-- |
-- | PureScript には標準的な Arrow ライブラリがないため、
-- | Noema 用に必要な部分のみを実装する。
-- |
-- | ## 圏論的構造
-- |
-- | Arrow は以下の構造を持つ:
-- | - Category: 恒等射 identity と合成 >>>
-- | - Arrow: arr による純粋関数の持ち上げ、first による強度
-- |
-- | ArrowChoice は意図的に定義しない。
-- | これにより Noema の Intent で分岐を型レベルで禁止する。
module Control.Arrow
  ( class Arrow
  , arr
  , first
  , second
  , split
  , fanout
  , (***) 
  , (&&&)
  ) where

import Prelude

import Control.Category (class Category, identity, (<<<), (>>>))
import Data.Tuple (Tuple(..), fst, snd, swap)

-- | Arrow 型クラス
-- |
-- | Category の拡張として、以下の操作を提供:
-- | - arr: 純粋関数を Arrow に持ち上げ
-- | - first: タプルの第一要素に Arrow を適用
-- |
-- | Arrow 法則:
-- | 1. arr identity = identity
-- | 2. arr (f >>> g) = arr f >>> arr g
-- | 3. first (arr f) = arr (first f)
-- | 4. first (f >>> g) = first f >>> first g
-- | 5. first f >>> arr fst = arr fst >>> f
-- | 6. first f >>> arr (identity *** g) = arr (identity *** g) >>> first f
-- | 7. first (first f) >>> arr assoc = arr assoc >>> first f
class Category a <= Arrow a where
  -- | 純粋関数を Arrow に持ち上げる
  arr :: forall b c. (b -> c) -> a b c
  
  -- | タプルの第一要素に Arrow を適用
  -- |
  -- | first f :: a (b, d) (c, d)
  first :: forall b c d. a b c -> a (Tuple b d) (Tuple c d)

-- | タプルの第二要素に Arrow を適用
-- |
-- | second f = arr swap >>> first f >>> arr swap
second :: forall a b c d. Arrow a => a b c -> a (Tuple d b) (Tuple d c)
second f = arr swap >>> first f >>> arr swap

-- | 二つの Arrow を並列に適用
-- |
-- | f *** g :: a (b, b') (c, c')
-- |
-- | (f *** g) (x, y) = (f x, g y)
split :: forall a b c b' c'. Arrow a => a b c -> a b' c' -> a (Tuple b b') (Tuple c c')
split f g = first f >>> second g

-- | split の中置演算子
infixr 3 split as ***

-- | 入力を複製して二つの Arrow に並列に適用
-- |
-- | f &&& g :: a b (c, c')
-- |
-- | (f &&& g) x = (f x, g x)
fanout :: forall a b c c'. Arrow a => a b c -> a b c' -> a b (Tuple c c')
fanout f g = arr (\b -> Tuple b b) >>> (f *** g)

-- | fanout の中置演算子
infixr 3 fanout as &&&

-- ============================================================
-- Function インスタンス
-- ============================================================

-- | 関数は Arrow
instance arrowFunction :: Arrow (->) where
  arr f = f
  first f (Tuple b d) = Tuple (f b) d

-- ============================================================
-- ArrowChoice は定義しない
-- ============================================================

-- | ArrowChoice を定義しないことで、以下が型エラーになる:
-- |
-- | ```purescript
-- | left :: a b c -> a (Either b d) (Either c d)   -- 存在しない
-- | right :: a b c -> a (Either d b) (Either d c)  -- 存在しない
-- | ```
-- |
-- | これにより Noema の Intent で分岐を型レベルで禁止する。
