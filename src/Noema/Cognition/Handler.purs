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
  , runHandler
  , composeHandlers
  ) where

import Prelude

import Control.Monad.Rec.Class (class MonadRec)
import Noema.Vorzeichnung.Intent (Intent', runIntent)

-- ============================================================
-- Handler の定義
-- ============================================================

-- | Handler: 語彙 f をモナド m で解釈
-- |
-- | Handler は自然変換 f ~> m として機能する。
-- | これにより Intent f a b を (a -> m b) に変換できる。
-- |
-- | Arrow 準同型性:
-- |   runHandler h (f >>> g) ≡ \a -> runHandler h f a >>= runHandler h g
-- |   runHandler h (arr f) ≡ pure <<< f
-- |   runHandler h (first f) ≡ \(a, c) -> (, c) <$> runHandler h f a
type Handler f m = f ~> m

-- | Handler を使って Intent を実行
-- |
-- | 圏論的解釈:
-- | Cognition（認知による忘却）の具体化。
-- | Intent（Vorzeichnungsschema）を解釈し、
-- | 具体的な効果という事実へ崩落させる。
-- |
-- | > 実行とは忘却である。
runHandler 
  :: forall f m a b
   . MonadRec m 
  => Handler f m 
  -> Intent' f a b 
  -> a 
  -> m b
runHandler = runIntent

-- ============================================================
-- Handler の合成
-- ============================================================

-- | Handler の合成（効果のリフト）
-- |
-- | h : f → m と lift : m → n に対して
-- | composeHandlers lift h : f → n
composeHandlers 
  :: forall f m n
   . (m ~> n)  -- モナド間の変換
  -> Handler f m 
  -> Handler f n
composeHandlers lift h = lift <<< h

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
-- | checkStock :: Intent' InventoryF Unit StockInfo
-- | checkStock = getStock thingId locationId
-- |
-- | -- Handler: 分岐を含む認知
-- | handleInventoryWithValidation :: InventoryF ~> Aff
-- | handleInventoryWithValidation (GetStock tid lid k) = do
-- |   info <- getStockFromDB tid lid
-- |   -- 分岐は Handler 層で行う
-- |   if info.available > Quantity 0
-- |     then do
-- |       _ <- adjustStockInDB tid lid (QuantityDelta (-1))
-- |       pure (k info)
-- |     else throwError (error "Out of stock")
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
-- | Intent ⊣ Cognition（随伴）
-- | 
-- | Handler h が右随伴 Cognition を実現:
-- | h : Intent f ~> Effect m
