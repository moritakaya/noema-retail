-- | Noema Topos: Nomos（法座標）
-- |
-- | 被覆構造（Grothendieck topology）としての法の規定。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Nomos はグロタンディーク・トポスにおける被覆構造に対応。
-- | 「どの操作が合法か」を規定し、Sediment の解釈を決定する。
-- | DO が眠って起きた時に Nomos が変わりうる（コードのデプロイ）。
-- |
-- | ## 哲学的背景
-- |
-- | Nomos（νόμος）はギリシャ語で「法」「規範」「慣習」。
-- | 大域意志として、Subject や Thing の振る舞いを規定する。
-- |
-- | ## 構造
-- |
-- | ```
-- | Nomos
-- | ├── 本則（Rules）: Lean4 で証明された規則
-- | └── 附則（SupplementaryProvisions）: 経過措置、適用開始時期
-- | ```
-- |
-- | ## Connection（位相論的接続）
-- |
-- | Nomos バージョン間の「連続的な平行移動」を検証する。
-- | - Flat（平坦）: 連続的移行可能
-- | - Curved（湾曲）: 非連続、警告を伴う移行
-- | - Critical（臨界）: 即時適用必須（セキュリティ等）
module Noema.Topos.Nomos
  ( -- * NomosVersion
    NomosVersion(..)
    -- * NomosReference（契約が依拠する法）
  , NomosReference
    -- * World（法座標）
  , World
  , mkWorld
    -- * IntentContext
  , IntentContext
  , mkIntentContext
    -- * Nomos（法の構造）
  , Nomos
  , Rules
  , SupplementaryProvisions
  , ContractTransition(..)
  , ExceptionRule
    -- * Duration（期間）
  , Duration(..)
  , mkDuration
    -- * Connection（位相論的接続）
  , ConnectionType(..)
  , Reason
  , verifyConnection
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Noema.Topos.Situs (Timestamp)

-- ============================================================
-- NomosVersion
-- ============================================================

-- | Nomos のバージョン
-- | セマンティックバージョニングを想定
newtype NomosVersion = NomosVersion String

derive instance Newtype NomosVersion _
derive instance eqNomosVersion :: Eq NomosVersion
derive instance ordNomosVersion :: Ord NomosVersion
derive newtype instance showNomosVersion :: Show NomosVersion

-- ============================================================
-- NomosReference（契約が依拠する法）
-- ============================================================

-- | Nomos への参照（契約が依拠する法）
type NomosReference =
  { version :: NomosVersion
  , jurisdiction :: Maybe String  -- 法域（日本法、米国法など）
  , customTerms :: Maybe String   -- カスタム条項への参照
  }

-- ============================================================
-- World（法座標）
-- ============================================================

-- | World = Nomos の適用文脈（法座標）
-- |
-- | DO が眠って起きた時：
-- | - Locus は同じ
-- | - World が変わりうる
type World =
  { nomosVersion :: NomosVersion
  , region :: Maybe String
  , timestamp :: Timestamp
  }

-- | World を作成
mkWorld :: NomosVersion -> Timestamp -> World
mkWorld version ts =
  { nomosVersion: version
  , region: Nothing
  , timestamp: ts
  }

-- ============================================================
-- IntentContext
-- ============================================================

-- | Intent の文脈
-- | 意図の発信元と送信先の World を保持
type IntentContext =
  { origin :: World
  , target :: World
  }

-- | IntentContext を作成
mkIntentContext :: World -> World -> IntentContext
mkIntentContext origin target =
  { origin
  , target
  }

-- ============================================================
-- Duration（期間）
-- ============================================================

-- | Duration（期間、ミリ秒）
-- |
-- | 猶予期間等の時間間隔を表現。
newtype Duration = Duration Number

derive instance Newtype Duration _
derive instance eqDuration :: Eq Duration
derive instance ordDuration :: Ord Duration
derive newtype instance showDuration :: Show Duration

-- | Duration を作成（ミリ秒）
mkDuration :: Number -> Duration
mkDuration = Duration

-- ============================================================
-- Rules（本則）
-- ============================================================

-- | Rules（本則）
-- |
-- | 当面は型エイリアスとして定義。
-- | 将来は Lean4 で証明された規則の参照を保持。
-- |
-- | 設計ノート：
-- | - schemaVersion: SQLite スキーマのバージョン
-- | - constraints: CHECK 制約等
-- | - validations: ビジネスルール（将来は Lean4 で証明）
type Rules =
  { schemaVersion :: String           -- スキーマバージョン
  , constraints :: Array String       -- 制約（SQL CHECK等）
  , validations :: Array String       -- バリデーションルール
  }

-- ============================================================
-- ContractTransition（既存契約の移行方針）
-- ============================================================

-- | 既存契約の移行方針
-- |
-- | Nomos が改訂された時、既存の契約をどう扱うか。
-- |
-- | 実際の法律の「経過措置」に対応：
-- | - 消費税法附則：旧税率の経過措置
-- | - 民法改正：施行前の契約への適用
data ContractTransition
  = PreserveOldLaw       -- 旧法維持（例: 消費税の経過措置）
  | MigrateToNewLaw      -- 新法適用（一定期間後）
  | CaseByCase           -- Connection で動的判定

derive instance eqContractTransition :: Eq ContractTransition

instance showContractTransition :: Show ContractTransition where
  show PreserveOldLaw = "PreserveOldLaw"
  show MigrateToNewLaw = "MigrateToNewLaw"
  show CaseByCase = "CaseByCase"

-- ============================================================
-- ExceptionRule（例外規則）
-- ============================================================

-- | 例外規則
-- |
-- | 附則における例外的な取り扱いを定義。
-- | condition は当面 String だが、将来は型安全な表現に移行。
type ExceptionRule =
  { condition :: String       -- 条件（将来は型で表現）
  , treatment :: ContractTransition
  , expiresAt :: Maybe Timestamp
  }

-- ============================================================
-- SupplementaryProvisions（附則）
-- ============================================================

-- | 附則（経過措置）
-- |
-- | 実際の法律と同様、施行時期や既存契約への適用を規定。
-- |
-- | ## 実際の法律との対応
-- |
-- | 日本の法律には必ず「附則」がある：
-- | - 施行期日
-- | - 経過措置
-- | - 適用関係
-- |
-- | ## 例
-- |
-- | 消費税法附則（経過措置）：
-- | - effectiveFrom: 2019年10月1日
-- | - existingContracts: PreserveOldLaw（一定の要件を満たす場合）
-- | - gracePeriod: 6ヶ月
-- | - exceptions: 請負契約の特例等
type SupplementaryProvisions =
  { effectiveFrom :: Timestamp           -- 施行日
  , existingContracts :: ContractTransition  -- 既存契約の扱い
  , gracePeriod :: Maybe Duration        -- 猶予期間
  , exceptions :: Array ExceptionRule    -- 例外規則
  }

-- ============================================================
-- Nomos（法の構造）
-- ============================================================

-- | Nomos 本体（法の構造）
-- |
-- | 圏論的位置づけ：
-- | グロタンディーク・トポスにおける被覆構造。
-- | 「どの操作が合法か」を規定する。
-- |
-- | 構造：
-- | - version: バージョン識別子
-- | - rules: 本則（Lean4 で検証）
-- | - supplementary: 附則（経過措置）
-- | - predecessor: 前バージョンへの参照（変更履歴）
type Nomos =
  { version :: NomosVersion
  , rules :: Rules                         -- 本則（Lean4 で検証）
  , supplementary :: SupplementaryProvisions  -- 附則
  , predecessor :: Maybe NomosVersion      -- 前バージョンへの参照
  }

-- ============================================================
-- Connection（位相論的接続）
-- ============================================================

-- | Connection 判定の理由
type Reason = String

-- | Connection: Nomos バージョン間の接続判定
-- |
-- | ## 位相論的観点
-- |
-- | Nomos のバージョン空間上で、ある点から別の点への
-- | 「連続的な平行移動」が可能かを判定する。
-- |
-- | ## 三分類
-- |
-- | - Flat（平坦）: 平行移動が連続（構造が保存される）
-- |   - 既存の Intent はそのまま適用可能
-- |   - 例: ドキュメントの修正、パフォーマンス改善
-- |
-- | - Curved（湾曲）: 平行移動が非連続（警告を伴う）
-- |   - 既存の Intent は附則に従って処理
-- |   - 例: 予約上限の変更、スキーマの追加
-- |
-- | - Critical（臨界）: 即時に移行が必要
-- |   - 既存の Intent は即座に新法で再評価
-- |   - 例: セキュリティパッチ、法令対応
-- |
-- | ## 判例との関係
-- |
-- | Connection の判定に失敗した Intent は「判例」として記録され、
-- | 将来の Nomos 改訂に影響を与える。
data ConnectionType
  = Flat               -- 平坦：連続的移行可能
  | Curved Reason      -- 湾曲：非連続、警告を伴う
  | Critical Reason    -- 臨界：即時適用必須

derive instance eqConnectionType :: Eq ConnectionType

instance showConnectionType :: Show ConnectionType where
  show Flat = "Flat"
  show (Curved reason) = "(Curved " <> show reason <> ")"
  show (Critical reason) = "(Critical " <> show reason <> ")"

-- | Connection を検証
-- |
-- | Intent の target World と Attractor の現在の World を比較し、
-- | 移行の可否と方法を判定する。
-- |
-- | 現在の実装：
-- | - 同一バージョンなら Flat
-- | - 異なるバージョンなら Curved（将来は Lean4 で検証）
-- |
-- | 将来の拡張：
-- | - Lean4 サービスと連携して平坦性を検証
-- | - Nomos の附則を参照して判定
verifyConnection :: World -> World -> ConnectionType
verifyConnection origin target
  | origin.nomosVersion == target.nomosVersion = Flat
  | otherwise =
      -- 将来は Lean4 サービスと連携して判定
      Curved "Version mismatch (pending Lean4 verification)"
