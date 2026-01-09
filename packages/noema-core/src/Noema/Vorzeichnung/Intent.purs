-- | Noema Intent Module
-- |
-- | Freer Arrow の公開APIを提供する。
-- | 他のモジュールはこのモジュールからインポートする。
-- |
-- | ## 圏論的構造
-- |
-- | Intent f a b は:
-- | - Category: id, >>>
-- | - Arrow: arr, first, second, ***, &&&
-- | - ArrowChoice なし（分岐禁止）
-- |
-- | ## 設計上の注意
-- |
-- | 語彙（InventoryF等）は二項関手（Profunctor）として定義されるが、
-- | Intent 内部では存在型を使って単項関手として扱う。
-- | これにより、PureScript の型システムの制約内で Arrow を実現する。
-- |
-- | ## unsafeCoerce の使用について
-- |
-- | このモジュールには2箇所の unsafeCoerce がある：
-- |
-- | 1. `first` 関数（Arrow インスタンス, line 131）
-- | 2. `runIntent` 関数（Par ケース, line 215）
-- |
-- | ### 安全性の保証
-- |
-- | これらは **構築規律（construction discipline）** により安全が保証される：
-- |
-- | - `Par` コンストラクタは `first` 関数経由でのみ構築される
-- | - `first :: Intent f a b -> Intent f (Tuple a c) (Tuple b c)`
-- | - 存在型 `Exists (ParF f a b)` が型関係を隠蔽するため unsafeCoerce が必要
-- | - `runIntent` は `Par` の構築時に確立された型関係を復元する
-- |
-- | ### なぜ unsafeCoerce が必要か
-- |
-- | PureScript は rank-2 types や GADTs を完全にはサポートしていない。
-- | 存在型（Exists）を使った Arrow の並列合成（first/second/***）では、
-- | 中間型が隠蔽されるため、コンパイラは型の同一性を検証できない。
-- |
-- | ### 代替案と却下理由
-- |
-- | - **Profunctor ベース**: 型が複雑化し、語彙定義が煩雑になる
-- | - **Monad に制限**: Arrow の表現力を失う（並列合成不可）
-- | - **外部ライブラリ**: PureScript エコシステムに適切なものがない
-- |
-- | 現在の設計は、実用性と安全性のバランスを取った選択である。
module Noema.Vorzeichnung.Intent
  ( -- * Intent type
    Intent
  , Intent'
  , IntentF(..)
  , EffF(..)
  , SeqF(..)
  , ParF(..)
    -- * Smart constructors
  , liftEffect
  , liftEffectWith
  , arrIntent
  , mkIntent
    -- * Running
  , runIntent
  , hoistIntent
    -- * Category/Arrow re-exports
  , module CC
  , module Arrow
  ) where

import Prelude

import Control.Category (class Category, identity, compose, (<<<), (>>>)) as CC
import Control.Category (class Category, identity, (<<<), (>>>))
import Control.Arrow (class Arrow, arr, first, second, (***), (&&&)) as Arrow
import Control.Arrow (class Arrow, arr, first, second, (***), (&&&))
import Data.Tuple (Tuple(..))
import Data.Exists (Exists, mkExists, runExists)
import Control.Monad.Rec.Class (class MonadRec)
import Type.Proxy (Proxy)

-- ============================================================
-- Intent 型
-- ============================================================

-- | Intent: 入力 a から出力 b への意志の経路
-- |
-- | Arrow として設計され、ArrowChoice を持たない。
-- | これにより「前の結果を見て分岐」が型レベルで禁止される。
newtype Intent f a b = Intent (IntentF f a b)

-- | Intent の別名（語彙を明示する場合）
type Intent' f a b = Intent f a b

-- | Intent の内部表現
-- |
-- | 静的な構造として効果の「列」を表現する。
-- | 存在型を使用して中間型を隠蔽。
data IntentF :: (Type -> Type) -> Type -> Type -> Type
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
-- | 効果 f x を実行し、結果 x を変換して b を得る。
-- | 入力 a は現在の実装では無視される。
newtype EffF :: (Type -> Type) -> Type -> Type -> Type -> Type
newtype EffF f a b x = EffF
  { effect :: f x
  , post :: x -> b
  }

-- | 列合成ノード
-- |
-- | a → x → b の経路（x は存在量化）
newtype SeqF :: (Type -> Type) -> Type -> Type -> Type -> Type
newtype SeqF f a b x = SeqF
  { fst :: Intent f a x
  , snd :: Intent f x b
  }

-- | 並列合成ノード（first 用）
-- |
-- | (a, c) → (b, c) の経路（c は存在量化）
newtype ParF :: (Type -> Type) -> Type -> Type -> Type -> Type
newtype ParF f a b c = ParF
  { inner :: Intent f a b
  }

-- ============================================================
-- Semigroupoid instance
-- ============================================================

instance semigroupoidIntent :: Semigroupoid (Intent f) where
  compose (Intent g) (Intent f) =
    Intent (Seq (mkExists (SeqF { fst: Intent f, snd: Intent g })))

-- ============================================================
-- Category instance
-- ============================================================

instance categoryIntent :: Category (Intent f) where
  identity = Intent (Arr identity)

-- ============================================================
-- Arrow instance
-- ============================================================

instance arrowIntent :: Arrow (Intent f) where
  arr f = Intent (Arr f)

  -- Note: The existential encoding hides the type relationship between
  -- inner Intent and the resulting tuple Intent. We use unsafeCoerce to
  -- tell the compiler the types are correct. Type safety is ensured by
  -- only constructing Par via the `first` function.
  first intent = unsafeCoerce (Intent (Par (mkExists (ParF { inner: intent }))))

-- ============================================================
-- ArrowChoice は意図的に実装しない
-- ============================================================
-- 
-- instance arrowChoiceIntent :: ArrowChoice (Intent f) where
--   left = ...   -- ← これを実装しないことで分岐を禁止
--   right = ...
--
-- コンパイルエラー例:
--   left someIntent  -- Error: No instance for ArrowChoice (Intent f)

-- ============================================================
-- Smart constructors
-- ============================================================

-- | 純粋関数を Intent に持ち上げる
arrIntent :: forall f a b. (a -> b) -> Intent f a b
arrIntent = arr

-- | Intent を構築（arrIntent の別名）
mkIntent :: forall f a b. (a -> b) -> Intent f a b
mkIntent = arr

-- | 効果を Intent に持ち上げる
-- |
-- | 入力を無視して効果を実行し、結果を返す。
-- |
-- | ```purescript
-- | getStock :: Intent' InventoryF Unit StockInfo
-- | getStock = liftEffect (GetStock thingId locationId identity identity)
-- | ```
-- |
-- | 注: 語彙が Profunctor (f i o) として定義されている場合、
-- | liftEffect は「出力型」のみを使用する。
-- | 入力は Intent の合成で処理される。
liftEffect :: forall f a b. f b -> Intent f a b
liftEffect fb = Intent (Eff (mkExists (EffF { effect: fb, post: identity })))

-- | 効果を持ち上げ、結果を変換する
liftEffectWith :: forall f a b x. f x -> (x -> b) -> Intent f a b
liftEffectWith fx post = Intent (Eff (mkExists (EffF { effect: fx, post: post })))

-- ============================================================
-- Running Intent
-- ============================================================

-- | Intent を実行する
-- |
-- | Handler（自然変換 f ~> m）を用いて Intent を解釈する。
-- |
-- | Arrow 準同型性:
-- |   runIntent h (f >>> g) ≡ \a -> runIntent h f a >>= runIntent h g
-- |   runIntent h (arr f) ≡ pure <<< f
-- |   runIntent h (first f) ≡ \(a, c) -> (, c) <$> runIntent h f a
runIntent
  :: forall f m a b
   . MonadRec m
  => (forall x. f x -> m x)
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
    runExists (\(SeqF { fst: f, snd: g }) -> \a -> do
      x <- runIntent handler f a
      runIntent handler g x
    ) ex
  
  Par ex ->
    -- Note: Type safety is ensured by the construction of Intent via `first`
    -- The existential hides the tuple structure (Tuple a' c -> Tuple b' c),
    -- which matches (a -> b) when a = Tuple a' c and b = Tuple b' c.
    -- We use unsafeCoerce because PureScript can't verify this relationship.
    runExists (\(ParF { inner }) ->
      unsafeCoerce (\(Tuple a' c) -> do
        b' <- runIntent handler inner a'
        pure (Tuple b' c))
    ) ex

foreign import unsafeCoerce :: forall a b. a -> b

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
  Arr f -> Arr f
  
  Eff ex ->
    Eff (runExists (\(EffF { effect, post }) -> 
      mkExists (EffF { effect: nat effect, post: post })
    ) ex)
  
  Seq ex ->
    Seq (runExists (\(SeqF { fst: f, snd: g }) ->
      mkExists (SeqF 
        { fst: hoistIntent nat f
        , snd: hoistIntent nat g
        })
    ) ex)
  
  Par ex ->
    Par (runExists (\(ParF { inner }) ->
      mkExists (ParF { inner: hoistIntent nat inner })
    ) ex)
