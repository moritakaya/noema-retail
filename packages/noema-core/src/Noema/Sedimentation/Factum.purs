-- | Noema Sedimentation: Factum（事実）
-- |
-- | Interpretation（解釈）の結果として生じた事実。
-- | Sedimentation（沈殿）の前段階であり、まだ Seal されていない流動的な状態。
-- |
-- | ## 語源
-- |
-- | ラテン語 "factum" = "為されたこと"（facere の過去分詞）
-- | 英語 "fact" の語源。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Intent ⊣ Cognition 随伴において:
-- | - Intent: 自由関手（意志の構造を生成）
-- | - Cognition/Interpretation: 忘却関手（構造を事実に崩落）
-- | - Factum: 崩落の結果（Cognition の像）
-- |
-- | ## Sedimentation 層における位置
-- |
-- | ```
-- | Sedimentation/（沈殿）
-- | ├── Factum.purs      -- 解釈の結果（まだ流動的な事実）← このモジュール
-- | └── Seal.purs        -- 沈殿の証明（確定した事実）
-- |
-- | 流れ:
-- |   Factum（液体）→ Seal（固体）
-- |   ※ 沈殿過程は InventoryAttractor（noema-retail）等の DO で実装
-- | ```
-- |
-- | ## 「実行とは忘却である」
-- |
-- | ```
-- | Intent（可能性の構造）
-- |   ↓ Interpretation（解釈）
-- | Factum（事実）
-- |   ↓ collapse（忘却）
-- | Effect（外界への崩落）
-- | ```
-- |
-- | Factum から Effect への変換（collapse）が「忘却」を表現する。
-- | 構造は消え、可能性は一つの現実に押し潰される。
-- |
-- | ## 技術的実装
-- |
-- | Factum は Effect の newtype ラッパー。
-- | newtype によりゼロコスト抽象化を実現（ランタイムオーバーヘッドなし）。
-- | 型レベルで Effect との区別を表現し、誤用を防止する。
module Noema.Sedimentation.Factum
  ( Factum(..)
  , collapse
  , recognize
  , class MonadFactum
  , liftFactum
  ) where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, tailRecM)
import Data.Newtype (class Newtype)
import Effect (Effect)

-- ============================================================
-- Factum 型
-- ============================================================

-- | Factum: 解釈の結果として生じた事実
-- |
-- | Interpretation が Intent を解釈した結果。
-- | Attractor に沈殿する前の、まだ流動的な事実。
-- |
-- | newtype により Effect との区別を型レベルで表現。
-- | ゼロコスト抽象化（ランタイムオーバーヘッドなし）。
-- |
-- | 使用例:
-- | ```purescript
-- | processOrder :: InventoryIntent Unit OrderResult -> Factum OrderResult
-- | processOrder intent = runInterpretation inventoryInterpretation intent unit
-- | ```
newtype Factum a = Factum (Effect a)

derive instance Newtype (Factum a) _

-- ============================================================
-- Functor / Applicative / Monad インスタンス
-- ============================================================

derive newtype instance Functor Factum
derive newtype instance Apply Factum
derive newtype instance Applicative Factum
derive newtype instance Bind Factum
derive newtype instance Monad Factum

-- ============================================================
-- MonadRec インスタンス
-- ============================================================

-- | MonadRec インスタンス（スタック安全な再帰）
-- |
-- | Intent の realizeIntent は MonadRec を要求するため必須。
instance MonadRec Factum where
  tailRecM f a = Factum $ tailRecM (\x -> unwrapFactum (f x)) a
    where
      unwrapFactum :: forall b. Factum b -> Effect b
      unwrapFactum (Factum e) = e

-- ============================================================
-- Semigroup / Monoid インスタンス
-- ============================================================

derive newtype instance Semigroup a => Semigroup (Factum a)
derive newtype instance Monoid a => Monoid (Factum a)

-- ============================================================
-- 境界変換関数
-- ============================================================

-- | 事実を外界へ崩落させる（忘却）
-- |
-- | Factum から Effect への変換。
-- | FFI 境界やエントリーポイントで使用。
-- |
-- | > 実行とは忘却である。
-- | > 自由な構造は消え、可能性は一つの現実に押し潰される。
-- |
-- | 使用例:
-- | ```purescript
-- | -- エントリーポイント（外界との境界）
-- | processFetch :: Request -> Effect Response
-- | processFetch req = collapse do
-- |   result <- realizeInventoryIntent env intent unit
-- |   recognize $ jsonResponse result
-- | ```
collapse :: forall a. Factum a -> Effect a
collapse (Factum e) = e

-- | Effect を事実として認識する
-- |
-- | FFI 境界で Effect を Factum に持ち上げる。
-- | 外界からの入力を「事実」として内部に取り込む。
-- |
-- | 使用例:
-- | ```purescript
-- | -- FFI 関数のラッパー
-- | getHeader :: Request -> String -> Factum (Maybe String)
-- | getHeader req name = recognize $ _getHeader req name
-- | ```
recognize :: forall a. Effect a -> Factum a
recognize = Factum

-- ============================================================
-- MonadFactum 型クラス
-- ============================================================

-- | MonadFactum: Effect を Factum へ持ち上げる
-- |
-- | FFI 境界での変換を抽象化。
-- | Effect.Class.MonadEffect の対応物。
-- |
-- | 使用例:
-- | ```purescript
-- | logMessage :: forall m. MonadFactum m => String -> m Unit
-- | logMessage msg = liftFactum $ log msg
-- | ```
class Monad m <= MonadFactum m where
  liftFactum :: forall a. Effect a -> m a

instance MonadFactum Factum where
  liftFactum = Factum

-- ============================================================
-- 設計ノート
-- ============================================================

-- | ## なぜ Effect ではなく Factum を使うか
-- |
-- | 1. **哲学的一貫性**: Noema の語彙体系（Topos, Horizont, Vorzeichnung,
-- |    Cognition, Sedimentation）と整合
-- |
-- | 2. **意味の明確化**: `-> Effect Response` ではなく `-> Factum Response`
-- |    と書くことで、「事実としての応答」という意味が明確になる
-- |
-- | 3. **型安全性**: Effect と Factum を混同するとコンパイルエラー
-- |    これにより誤用を防止
-- |
-- | 4. **技術非依存**: PureScript が将来 Effect を変更しても、
-- |    Factum のインターフェースは維持可能
-- |
-- | ## collapse と recognize の対称性
-- |
-- | ```
-- | recognize : Effect → Factum  （認識: 外界 → 内部）
-- | collapse  : Factum → Effect  （忘却: 内部 → 外界）
-- | ```
-- |
-- | この対称性は Noema のアーキテクチャを反映:
-- | - 外界（Effect）と内部（Factum）の境界が明確
-- | - 変換は常に明示的
