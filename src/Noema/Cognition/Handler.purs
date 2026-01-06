-- | Noema Cognition: Handler（Arrow 準同型）
-- |
-- | Handler は Intent を具体的なエフェクトに解釈する。
-- | 圏論的には Arrow 準同型（Arrow Morphism）。
-- |
-- | 重要な制約:
-- | - Handler は Arrow 構造を保存する
-- | - 分岐の導入は Handler の層でのみ可能
-- | - 「実行とは忘却である」
module Noema.Cognition.Handler
  ( Handler
  , ArrowHandler
  , runHandler
  , composeHandlers
  -- Handler laws
  , HandlerLaws
  , verifyArrowPreservation
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Tuple (Tuple(..))
import Data.Profunctor (class Profunctor)

import Noema.Vorzeichnung.Intent (Intent', runIntent)

-- ============================================================
-- Handler の定義
-- ============================================================

-- | Handler: エフェクト f を モナド m で解釈
-- |
-- | Handler は二項関手間の自然変換:
-- | h : f → (→ m)
-- |
-- | ただし、(→ m) は Kleisli Arrow:
-- | (a → m b) を表す
type Handler f m = forall a b. f a b -> a -> m b

-- | ArrowHandler: Intent 全体の解釈
-- |
-- | Handler から導出される Intent の解釈関数
type ArrowHandler f m = forall i o. Intent' f i o -> i -> m o

-- | Handler を使って Intent を実行
runHandler :: forall f m i o. Monad m => Handler f m -> Intent' f i o -> i -> m o
runHandler = runIntent

-- ============================================================
-- Handler の合成
-- ============================================================

-- | Handler の合成
-- |
-- | h1 : f → m, h2 : m → n に対して
-- | h2 ∘ h1 : f → n
-- |
-- | 注意: これは Handler 自体の合成ではなく、
-- | 効果の層での合成を表す
composeHandlers 
  :: forall f m n
   . Monad m
  => Monad n
  => (forall a. m a -> n a)  -- モナド間の変換
  -> Handler f m 
  -> Handler f n
composeHandlers lift h = \eff a -> lift (h eff a)

-- ============================================================
-- Handler Laws（Arrow 準同型性）
-- ============================================================

-- | Handler が満たすべき法則
-- |
-- | Arrow 準同型として:
-- | 1. h (arr f) = arr f               -- 純粋関数の保存
-- | 2. h (f >>> g) = h f >>> h g       -- 合成の保存
-- | 3. h (first f) = first (h f)       -- 強度の保存
-- |
-- | これらは「Handler が構造を保存する」ことを意味する。
-- |
-- | Monad を経由する場合、Kleisli Arrow で考える:
-- | h f : a -> m b
-- | h g : b -> m c
-- | h (f >>> g) : a -> m c = \a -> h f a >>= h g
type HandlerLaws f m =
  { arrPreservation :: forall a b. (a -> b) -> Boolean
  , composePreservation :: forall a b c. Intent' f a b -> Intent' f b c -> Boolean
  , firstPreservation :: forall a b d. Intent' f a b -> Boolean
  }

-- | Arrow 構造の保存を検証
-- |
-- | テストで使用
verifyArrowPreservation 
  :: forall f m a b c
   . Monad m
  => Eq (m c)
  => Handler f m
  -> Intent' f a b
  -> Intent' f b c
  -> a
  -> Boolean
verifyArrowPreservation h f g a =
  -- h (f >>> g) = h f >>> h g（Kleisli 合成で）
  let
    -- 左辺: h (f >>> g)
    composed = runHandler h (f >>> g) a
    
    -- 右辺: h f >>> h g（Kleisli 合成）
    -- = \a -> h f a >>= h g
    sequential = do
      b <- runHandler h f a
      runHandler h g b
  in
    composed == sequential

-- ============================================================
-- 分岐の扱い
-- ============================================================

-- | 分岐が必要な場合の設計パターン
-- |
-- | Intent（意志）の層では分岐を禁止し、
-- | Handler（認知）の層で分岐を処理する。
-- |
-- | 例: 在庫があれば調整、なければエラー
-- |
-- | ```purescript
-- | -- Intent: 分岐なし、線形
-- | checkAndAdjust :: Intent' InventoryF Unit StockInfo
-- | checkAndAdjust = getStock thingId locationId
-- |
-- | -- Handler: 分岐を含む認知
-- | handleWithBranching :: Handler InventoryF Aff
-- | handleWithBranching (GetStock tid lid fi fo) a = do
-- |   info <- getStockFromDB tid lid
-- |   if info.available > Quantity 0
-- |     then adjustStockInDB tid lid (QuantityDelta (-1))
-- |     else throwError "Out of stock"
-- |   pure (fo info)
-- | ```
-- |
-- | これにより:
-- | - Intent は純粋な「意志の表明」
-- | - 分岐は「認知の結果」として Handler で処理
-- | - 「実行とは忘却である」の原則を維持

-- ============================================================
-- Cognition としての解釈
-- ============================================================

-- | Cognition: 忘却関手
-- |
-- | Handler は Cognition の実現:
-- | - Intent（自由な意志）を Effect（具体的な事実）に崩落させる
-- | - 構造は保存されるが、可能性の豊かさは失われる
-- |
-- | 圏論的には:
-- | Intent ⊣ Cognition
-- | 
-- | Handler h が右随伴 Cognition を実現:
-- | h : Intent f ~> Effect m
-- |
-- | 随伴の単位・余単位:
-- | η : Id → Cognition ∘ Intent    （意志を認知に持ち上げ）
-- | ε : Intent ∘ Cognition → Id    （認知を意志で解釈）

-- | Handler の型クラス表現
class Cognition f m where
  cognize :: Handler f m

-- | デフォルトの Handler インスタンスは各モジュールで提供
-- |
-- | 例: Noema.Cognition.InventoryHandler
-- |
-- | instance cognitionInventoryAff :: Cognition InventoryF Aff where
-- |   cognize = inventoryHandler
