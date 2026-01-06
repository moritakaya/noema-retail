-- | Noema Intent: Freer Arrow（継続ベース実装）
-- |
-- | 意志（Intent）を Freer Arrow として定式化する。
-- | 継続渡しスタイル（CPS）による効率的な実装。
-- |
-- | 設計の核心:
-- | 1. ArrowChoice を持たない → 分岐を型レベルで禁止
-- | 2. 静的に構造が確定 → 最適化・解析が可能
-- | 3. Arrow 法則を満たす → 代数的推論が可能
module Noema.Vorzeichnung.Intent
  ( Intent(..)
  , Effect(..)
  , runIntent
  , liftEffect
  , arrIntent
  -- Arrow combinators
  , (>>>)
  , (<<<)
  , first
  , second
  , (***)
  , (&&&)
  -- Smart constructors for testing
  , pureIntent
  ) where

import Prelude hiding ((>>>), (<<<))

import Data.Tuple (Tuple(..), fst, snd)
import Data.Either (Either(..))
import Data.Profunctor (class Profunctor, dimap)

-- | Effect: 二項関手としてのエフェクト
-- |
-- | 入力型 `i` を受け取り、出力型 `o` を生成する操作。
-- | 単項関手 f a と異なり、入出力の型が明示される。
class Effect (f :: Type -> Type -> Type) where
  -- | エフェクトに対する Profunctor インスタンスが必要
  effectDimap :: forall a b c d. (a -> b) -> (c -> d) -> f b c -> f a d

-- | Intent: Freer Arrow
-- |
-- | データ型としての GADT 風表現。
-- | PureScript では GADT がないため、タグ付きユニオンで模倣。
data Intent f i o
  = Pure (i -> o)
  | Lift (f i o)
  | Compose (IntentCompose f i o)
  | First (IntentFirst f i o)

-- | 合成の内部表現
-- | 中間型を隠蔽するための存在型的構造
newtype IntentCompose f i o = IntentCompose
  { first :: Intent f i (ComposeMiddle f i o)
  , second :: Intent f (ComposeMiddle f i o) o
  }

-- | first の内部表現
newtype IntentFirst f i o = IntentFirst
  { inner :: Intent f (FirstInner f i o) (FirstOuter f i o)
  , extract :: i -> Tuple (FirstInner f i o) (FirstExtra f i o)
  , combine :: Tuple (FirstOuter f i o) (FirstExtra f i o) -> o
  }

-- | 型レベルでの中間型（実際の実装では具体化される）
foreign import data ComposeMiddle :: (Type -> Type -> Type) -> Type -> Type -> Type
foreign import data FirstInner :: (Type -> Type -> Type) -> Type -> Type -> Type
foreign import data FirstOuter :: (Type -> Type -> Type) -> Type -> Type -> Type
foreign import data FirstExtra :: (Type -> Type -> Type) -> Type -> Type -> Type

-- | 単純化された実装（実用版）
-- |
-- | 上記の複雑な型を避け、より実用的な表現を使用
data IntentSimple f i o
  = PureS (i -> o)
  | LiftS (f i o)
  | forall m. ComposeS (IntentSimple f i m) (IntentSimple f m o)
  | forall a b d. FirstS (IntentSimple f a b) (i -> Tuple a d) (Tuple b d -> o)

-- | 実用的な Intent 型（簡易版）
-- |
-- | 型安全性を維持しつつ、実装を簡潔にする
newtype IntentP f i o = IntentP (forall r. IntentK f i o r -> r)

-- | 継続ベースの Intent 表現
data IntentK f i o r
  = KPure (i -> o) ((i -> o) -> r)
  | KLift (f i o) (f i o -> r)
  | forall m. KCompose (IntentP f i m) (IntentP f m o) (IntentP f i o -> r)
  | forall a b d. KFirst (IntentP f a b) (IntentP f (Tuple a d) (Tuple b d) -> r)

-- ============================================================
-- 実際に使用する実装（型を具体化）
-- ============================================================

-- | Intent の最終的な定義
-- |
-- | GADT の代わりにスマートコンストラクタパターンを使用
newtype Intent' f i o = Intent' (IntentRepr f i o)

data IntentRepr f i o
  = RPure (i -> o)
  | RLift (f i o)
  | RSeq (SeqRepr f i o)
  | RFirst (FirstRepr f i o)

-- | 直列合成の表現
-- | 中間型を外部に公開しない
data SeqRepr f i o = forall m. SeqRepr (Intent' f i m) (Intent' f m o)

-- | First の表現
data FirstRepr f i o = forall a b d. FirstRepr 
  (Intent' f a b) 
  (i -> Tuple a d) 
  (Tuple b d -> o)

-- ============================================================
-- Arrow インスタンス
-- ============================================================

-- | 直列合成
infixr 1 composeIntent as >>>
infixr 1 composeIntentFlipped as <<<

composeIntent :: forall f i m o. Intent' f i m -> Intent' f m o -> Intent' f i o
composeIntent f g = Intent' (RSeq (SeqRepr f g))

composeIntentFlipped :: forall f m o i. Intent' f m o -> Intent' f i m -> Intent' f i o
composeIntentFlipped g f = composeIntent f g

-- | 純粋関数の埋め込み
arrIntent :: forall f i o. (i -> o) -> Intent' f i o
arrIntent f = Intent' (RPure f)

-- | エフェクトの持ち上げ
liftEffect :: forall f i o. f i o -> Intent' f i o
liftEffect eff = Intent' (RLift eff)

-- | First（強度）
first :: forall f a b d. Intent' f a b -> Intent' f (Tuple a d) (Tuple b d)
first (Intent' inner) = Intent' (RFirst (FirstRepr (Intent' inner) identity identity))

-- | Second
second :: forall f a b d. Intent' f a b -> Intent' f (Tuple d a) (Tuple d b)
second f = arrIntent swap >>> first f >>> arrIntent swap
  where
    swap :: forall x y. Tuple x y -> Tuple y x
    swap (Tuple x y) = Tuple y x

-- | 並列合成
infixr 3 parallelIntent as ***

parallelIntent :: forall f a b c d. Intent' f a b -> Intent' f c d -> Intent' f (Tuple a c) (Tuple b d)
parallelIntent f g = first f >>> second g

-- | ファンアウト
infixr 3 fanoutIntent as &&&

fanoutIntent :: forall f a b c. Intent' f a b -> Intent' f a c -> Intent' f a (Tuple b c)
fanoutIntent f g = arrIntent dup >>> parallelIntent f g
  where
    dup :: forall x. x -> Tuple x x
    dup x = Tuple x x

-- | 純粋な Intent（テスト用）
pureIntent :: forall f a. a -> Intent' f Unit a
pureIntent a = arrIntent (const a)

-- ============================================================
-- インタープリター
-- ============================================================

-- | Intent を実行する
-- |
-- | Handler h : f → m に対して、Intent f i o を m (i -> o) に変換
-- | 
-- | 注意: Arrow の解釈は Monad とは異なる。
-- | 結果は「i -> m o」ではなく「m (i -> o)」となる場合がある。
runIntent 
  :: forall f m i o
   . Monad m
  => (forall a b. f a b -> a -> m b)  -- Handler
  -> Intent' f i o 
  -> i
  -> m o
runIntent h (Intent' repr) = case repr of
  RPure f -> \i -> pure (f i)
  RLift eff -> h eff
  RSeq (SeqRepr f g) -> \i -> do
    m <- runIntent h f i
    runIntent h g m
  RFirst (FirstRepr inner extract combine) -> \i -> do
    let Tuple a d = extract i
    b <- runIntent h inner a
    pure (combine (Tuple b d))

-- ============================================================
-- 重要: ArrowChoice は実装しない
-- ============================================================

-- | 以下のコードは意図的にコメントアウト
-- | ArrowChoice を実装すると分岐が可能になってしまう
-- |
-- | class Arrow a <= ArrowChoice a where
-- |   left :: a b c -> a (Either b d) (Either c d)
-- |
-- | instance arrowChoiceIntent :: ArrowChoice (Intent f) where
-- |   left = ...  -- 実装しない!

-- | 分岐を試みると型エラー:
-- |
-- | illegalBranching :: Intent InventoryF (Either Int String) (Either Int String)
-- | illegalBranching = left someEffect  -- 型エラー: No instance for ArrowChoice (Intent f)

-- ============================================================
-- Category / Semigroupoid インスタンス
-- ============================================================

instance semigroupoidIntent :: Semigroupoid (Intent' f) where
  compose = composeIntentFlipped

instance categoryIntent :: Category (Intent' f) where
  identity = arrIntent identity

-- | Profunctor インスタンス
instance profunctorIntent :: Profunctor (Intent' f) where
  dimap f g intent = arrIntent f >>> intent >>> arrIntent g
