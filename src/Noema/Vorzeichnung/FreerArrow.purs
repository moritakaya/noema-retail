-- | Noema Intent: Freer Arrow
-- |
-- | 意志（Intent）を Freer Arrow として定式化する。
-- | ArrowChoice を持たないことで、「前の結果を見て分岐」を型レベルで禁止する。
-- |
-- | 圏論的構造：
-- | - Intent は自由 Arrow（Free Category over f）
-- | - Arrow ≃ 強度付き Profunctor
-- | - ArrowChoice の不在 → 分岐の禁止
-- |
-- | 哲学的基盤：
-- | > 意図は実行前に完全に記述される。
-- | > 分岐は「認知」の領域であり、「意志」の領域ではない。
-- | > 実行とは忘却である。
module Noema.Vorzeichnung.FreerArrow
  ( FreerArrow
  , Intent
  , liftEffect
  , runArrow
  , (>>>)
  , (<<<)
  , arr
  , first
  , second
  , (***)
  , (&&&)
  ) where

import Prelude hiding ((>>>), (<<<))
import Data.Tuple (Tuple(..), fst, snd, swap)
import Data.Profunctor (class Profunctor, dimap)
import Effect.Aff (Aff)

-- | Freer Arrow: 効果 f に対する自由 Arrow
-- |
-- | データ構造としての表現:
-- | - Arr: 純粋関数の埋め込み
-- | - Effect: エフェクトの持ち上げ
-- | - Seq: 直列合成
-- | - Par: 並列合成（first の実現）
data FreerArrow f a b
  = Arr (a -> b)
  | Effect (f a b)
  | Seq (Exists (SeqF f a b))
  | Par (Exists (ParF f a b))

-- | 直列合成の内部表現
-- | FreerArrow f a b と FreerArrow f b c から FreerArrow f a c を構成
data SeqF f a c x = SeqF (FreerArrow f a x) (FreerArrow f x c)

-- | 並列合成の内部表現（first の実現）
-- | FreerArrow f a b から FreerArrow f (a, d) (b, d) を構成
data ParF f a' b' x = ParF (FreerArrow f x b') -- ここで x が隠蔽される

-- | 存在型のエンコーディング（PureScript では手動）
foreign import data Exists :: (Type -> Type) -> Type

foreign import mkExists :: forall f a. f a -> Exists f
foreign import runExists :: forall f r. (forall a. f a -> r) -> Exists f -> r

-- | Intent: 小売ドメインの意志
-- | 具体的な語彙 f に対する FreerArrow
type Intent f = FreerArrow f

-- | エフェクトを Intent に持ち上げる
-- |
-- | 圏論的解釈: η : f → FreerArrow f（単位射）
liftEffect :: forall f a b. f a b -> FreerArrow f a b
liftEffect = Effect

-- | 純粋関数を Arrow に持ち上げる
-- |
-- | Arrow 法則: arr id = id
-- | Arrow 法則: arr (g <<< f) = arr g <<< arr f
arr :: forall f a b. (a -> b) -> FreerArrow f a b
arr = Arr

-- | 直列合成
-- |
-- | Arrow 法則: (f >>> g) >>> h = f >>> (g >>> h)
-- | Arrow 法則: arr id >>> f = f = f >>> arr id
infixr 1 compose as >>>
infixr 1 composeFlipped as <<<

compose :: forall f a b c. FreerArrow f a b -> FreerArrow f b c -> FreerArrow f a c
compose f g = case f, g of
  -- 最適化: arr の合成
  Arr f', Arr g' -> Arr (g' <<< f')
  -- 最適化: 恒等射との合成
  Arr f', _ | isId f' -> g
  _, Arr g' | isId g' -> f
  -- 一般ケース
  _, _ -> Seq (mkExists (SeqF f g))
  where
    isId :: forall x y. (x -> y) -> Boolean
    isId _ = false  -- 実行時には判定不可能、型レベルでは不要

composeFlipped :: forall f a b c. FreerArrow f b c -> FreerArrow f a b -> FreerArrow f a c
composeFlipped g f = compose f g

-- | first: 強度
-- |
-- | Arrow 法則: first (arr f) = arr (bimap f id)
-- | Arrow 法則: first (f >>> g) = first f >>> first g
-- | Arrow 法則: first f >>> arr fst = arr fst >>> f
first :: forall f a b d. FreerArrow f a b -> FreerArrow f (Tuple a d) (Tuple b d)
first fa = case fa of
  -- 最適化: arr の first
  Arr f -> Arr (\(Tuple a d) -> Tuple (f a) d)
  -- 一般ケース: 実際の実装はもう少し複雑
  _ -> unsafeCoerce fa  -- TODO: 正しい実装

-- | second: first の双対
second :: forall f a b d. FreerArrow f a b -> FreerArrow f (Tuple d a) (Tuple d b)
second f = arr swap >>> first f >>> arr swap

-- | (***): 並列合成
infixr 3 parallel as ***

parallel :: forall f a b c d. FreerArrow f a b -> FreerArrow f c d -> FreerArrow f (Tuple a c) (Tuple b d)
parallel f g = first f >>> second g

-- | (&&&): ファンアウト
infixr 3 fanout as &&&

fanout :: forall f a b c. FreerArrow f a b -> FreerArrow f a c -> FreerArrow f a (Tuple b c)
fanout f g = arr (\x -> Tuple x x) >>> (f *** g)

-- | FreerArrow を解釈する
-- |
-- | Handler h : f → g に対して、FreerArrow f を FreerArrow g に変換
-- | これは Arrow 圏の間の関手
runArrow 
  :: forall f g a b
   . (forall x y. f x y -> g x y)  -- Handler
  -> FreerArrow f a b 
  -> FreerArrow g a b
runArrow _ (Arr f) = Arr f
runArrow h (Effect eff) = Effect (h eff)
runArrow h (Seq ex) = runExists (\(SeqF f g) -> runArrow h f >>> runArrow h g) ex
runArrow h (Par ex) = runExists (\(ParF f) -> unsafeCoerce (runArrow h f)) ex  -- TODO

-- | Category インスタンス
instance categoryFreerArrow :: Category (FreerArrow f) where
  identity = Arr identity
  compose = composeFlipped

-- | Semigroupoid インスタンス
instance semigroupoidFreerArrow :: Semigroupoid (FreerArrow f) where
  compose = composeFlipped

-- | Profunctor インスタンス（Arrow の前提）
instance profunctorFreerArrow :: Profunctor (FreerArrow f) where
  dimap f g fa = arr f >>> fa >>> arr g

-- | 注意: ArrowChoice は意図的に実装しない
-- | これにより以下のコードは型エラーになる:
-- |
-- | > left :: FreerArrow f a b -> FreerArrow f (Either a c) (Either b c)
-- | > left fa = ...  -- 実装不可能
-- |
-- | > illegalBranching = left (liftEffect someEffect)  -- 型エラー!

-- FFI プレースホルダー
foreign import unsafeCoerce :: forall a b. a -> b
