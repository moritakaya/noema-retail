-- | Noema Cognition: Interpretation（解釈）
-- |
-- | Intent（意図）を Factum（事実）へ解釈する。
-- | 圏論的には Arrow 準同型（Arrow Morphism）。
-- |
-- | ## 現象学的背景
-- |
-- | Husserl 現象学における「解釈」(Auslegung)。
-- | 意識が意味内容（Noema）を構成する作用。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Intent ⊣ Cognition 随伴において:
-- | - Intent: 自由関手（意志の構造を生成）
-- | - Interpretation: Cognition（忘却関手）の具体的実現
-- | - 自然変換 f ~> Factum として機能
-- |
-- | ## 技術的語彙からの移行
-- |
-- | 旧名称「Handler」から「Interpretation」へ変更。
-- |
-- | 理由:
-- | 1. 技術は進歩し変化するが、哲学・意味論は安定している
-- | 2. Noema の語彙体系（Topos, Horizont, Vorzeichnung, Cognition,
-- |    Sedimentation）と整合
-- | 3. 「意味→技術→意味」ではなく「意味→意味」の直接的対話を実現
-- |
-- | ## 重要な制約
-- |
-- | - Interpretation は Arrow 構造を保存する
-- | - 分岐の導入は Interpretation の層でのみ可能
-- | - Intent 層では分岐禁止（ArrowChoice なし）
-- |
-- | ## 「実行とは忘却である」
-- |
-- | Interpretation が Intent を Factum に変換する過程で、
-- | 意志の構造は忘却され、一つの事実へと崩落する。
-- |
-- | ```
-- | Intent（可能性の構造）
-- |   ↓ Interpretation（解釈）
-- | Factum（事実）
-- |   ↓ collapse（忘却）
-- | Effect（外界への崩落）
-- | ```
module Noema.Cognition.Interpretation
  ( Interpretation
  , runInterpretation
  , composeInterpretations
  ) where

import Prelude

import Noema.Sedimentation.Factum (Factum)
import Noema.Vorzeichnung.Intent (Intent', runIntent)

-- ============================================================
-- Interpretation の定義
-- ============================================================

-- | Interpretation: 語彙 f を Factum で解釈
-- |
-- | 自然変換 f ~> Factum として機能。
-- | Intent f a b を (a -> Factum b) に変換できる。
-- |
-- | Arrow 準同型性:
-- |   runInterpretation h (f >>> g) ≡ \a -> runInterpretation h f a >>= runInterpretation h g
-- |   runInterpretation h (arr f) ≡ pure <<< f
-- |   runInterpretation h (first f) ≡ \(a, c) -> (, c) <$> runInterpretation h f a
-- |
-- | 使用例:
-- | ```purescript
-- | interpretInventoryF :: InventoryEnv -> Interpretation InventoryF
-- | interpretInventoryF env = case _ of
-- |   GetStock tid sid k -> do
-- |     cursor <- recognize $ execWithParams env.sql ...
-- |     ...
-- | ```
type Interpretation f = forall x. f x -> Factum x

-- ============================================================
-- Intent の実行
-- ============================================================

-- | Interpretation を使って Intent を実行
-- |
-- | 圏論的解釈:
-- | Cognition（認知による忘却）の具体化。
-- | Intent（Vorzeichnungsschema）を解釈し、
-- | Factum（事実）へ崩落させる。
-- |
-- | > 実行とは忘却である。
-- |
-- | 使用例:
-- | ```purescript
-- | runInventoryIntent :: InventoryEnv -> InventoryIntent a b -> a -> Factum b
-- | runInventoryIntent env intent input =
-- |   runInterpretation (interpretInventoryF env) intent input
-- | ```
runInterpretation
  :: forall f a b
   . Interpretation f
  -> Intent' f a b
  -> a
  -> Factum b
runInterpretation = runIntent

-- ============================================================
-- Interpretation の合成
-- ============================================================

-- | Interpretation の合成
-- |
-- | 複数の Interpretation を合成する。
-- | モナド変換子のリフトに相当。
-- |
-- | 使用例:
-- | ```purescript
-- | -- ログ機能を追加
-- | withLogging :: Interpretation f -> Interpretation f
-- | withLogging = composeInterpretations addLogging
-- |   where
-- |     addLogging :: Factum ~> Factum
-- |     addLogging fa = do
-- |       recognize $ log "Before execution"
-- |       result <- fa
-- |       recognize $ log "After execution"
-- |       pure result
-- | ```
composeInterpretations
  :: forall f
   . (Factum ~> Factum)
  -> Interpretation f
  -> Interpretation f
composeInterpretations lift h = lift <<< h

-- ============================================================
-- 分岐の扱い
-- ============================================================

-- | 分岐が必要な場合の設計パターン
-- |
-- | Intent（意志）の層では分岐を禁止し、
-- | Interpretation（解釈）の層で分岐を処理する。
-- |
-- | 例: 在庫があれば調整、なければエラー
-- |
-- | ```purescript
-- | -- Intent: 分岐なし、線形
-- | checkStock :: Intent' InventoryF Unit StockInfo
-- | checkStock = getStock thingId subjectId
-- |
-- | -- Interpretation: 分岐を含む解釈
-- | interpretWithValidation :: InventoryF ~> Factum
-- | interpretWithValidation (GetStock tid sid k) = do
-- |   info <- getStockFromDB tid sid
-- |   -- 分岐は Interpretation 層で行う
-- |   if info.available > Quantity 0
-- |     then do
-- |       _ <- adjustStockInDB tid sid (QuantityDelta (-1))
-- |       pure (k info)
-- |     else throwError (error "Out of stock")
-- | ```
-- |
-- | これにより:
-- | - Intent は純粋な「意志の表明」
-- | - 分岐は「解釈の結果」として Interpretation で処理
-- | - 「実行とは忘却である」の原則を維持

-- ============================================================
-- Cognition としての解釈
-- ============================================================

-- | Cognition: 忘却関手
-- |
-- | Interpretation は Cognition の実現:
-- | - Intent（自由な意志）を Factum（事実）に崩落させる
-- | - 構造は保存されるが、可能性の豊かさは失われる
-- |
-- | 圏論的には:
-- | Intent ⊣ Cognition（随伴）
-- |
-- | Interpretation h が右随伴 Cognition を実現:
-- | h : Intent f ~> Factum
