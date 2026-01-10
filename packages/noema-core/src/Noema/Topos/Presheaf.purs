-- | Noema Topos: Presheaf（前層 / ステージング環境）
-- |
-- | 圏論的位置づけ:
-- |   - Set^{C^op}（Site 上の前層圏）
-- |   - 層化関手 a: Presheaf → Sheaf の入力
-- |   - Sedimentation（沈殿）により層化される
-- |
-- | ## 哲学的基盤
-- |
-- | Presheaf はまだ沈殿していない状態を表現する。
-- | 意志（Intent）は Presheaf として構造化され、
-- | Cognition を通じて層（Sheaf = 事実）へと崩落する。
-- |
-- | ```
-- | Presheaf（前層）
-- |     ↓ 層化関手 a
-- | Sheaf（層）= Sedimentation の結果
-- | ```
-- |
-- | ## ステージング環境としての役割
-- |
-- | Presheaf は以下の用途で使用される：
-- | - 複数の Intent をバッチ処理前にステージング
-- | - トランザクション境界の管理
-- | - 投機的実行と確定的実行の区別
-- | - 異常実行時の Intent 構造保存（preservedZippers）
-- |
-- | ## StagingState と StagingOutcome の分離
-- |
-- | Noema では「Sediment は不変」という原則がある。
-- | そのため、ステージングの「進行状態」と「結果」を分離する：
-- |
-- | - StagingState: 進行状態（Pending → Processing → Completed）
-- | - StagingOutcome: 結果（Sedimented / Abandoned / Rejected）
-- |
-- | Rejected は「判例」として記録され、将来の Nomos 改訂に影響を与える。
-- |
-- | ## 異常実行時の Intent 保存（preservedZippers）
-- |
-- | 「実行とは忘却である」の原則に従い、正常実行時は Intent 構造は忘却される。
-- | しかし異常実行時は Intent 構造を保存し、再実行を可能にする。
-- |
-- | - 正常実行（Forgotten）: Intent は忘却、結果のみが残る
-- | - 異常実行（Preserved）: IntentZipper として構造を保存
-- |
-- | 保存された IntentZipper は Presheaf の preservedZippers フィールドに蓄積され、
-- | 後から検査・再実行が可能。
module Noema.Topos.Presheaf
  ( -- * Presheaf
    Presheaf
  , emptyPresheaf
  , stage
  , complete
  , preserveZipper
    -- * StagingId
  , StagingId(..)
  , mkStagingId
    -- * StagingState
  , StagingState(..)
    -- * StagingOutcome
  , StagingOutcome(..)
  , Reason
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Argonaut.Core (Json)
import Noema.Topos.Situs (Timestamp, SubjectId, SedimentId)
import Noema.Topos.Nomos (World)

-- ============================================================
-- StagingId
-- ============================================================

-- | ステージング ID
newtype StagingId = StagingId String

derive instance eqStagingId :: Eq StagingId
derive instance ordStagingId :: Ord StagingId
derive newtype instance showStagingId :: Show StagingId

mkStagingId :: String -> StagingId
mkStagingId = StagingId

-- ============================================================
-- StagingState（進行状態）
-- ============================================================

-- | ステージングの進行状態
-- |
-- | Presheaf のライフサイクルを表現する。
-- | RolledBack は存在しない：Noema では Sediment は不変であり、
-- | 「ロールバック」という概念は StagingOutcome.Abandoned として表現される。
data StagingState
  = Pending       -- 保留中（Intent を蓄積中）
  | Processing    -- 処理中（Sedimentation 実行中）
  | Completed     -- 完了（結果は outcome フィールドを参照）

derive instance eqStagingState :: Eq StagingState

instance showStagingState :: Show StagingState where
  show Pending = "Pending"
  show Processing = "Processing"
  show Completed = "Completed"

-- ============================================================
-- StagingOutcome（結果）
-- ============================================================

-- | 結果の理由
type Reason = String

-- | ステージングの結果
-- |
-- | Cognition が Intent を解釈した結果。
-- | 一度決定したら不変（Noema の原則）。
-- |
-- | ## 判例（Case Law）
-- |
-- | Rejected は「判例」として記録される。
-- | Noema には「エラー」という概念はない。
-- | Cognition が正常に崩落しなかったケースは全て判例となり、
-- | 将来の Nomos 改訂（立法）に影響を与える。
-- |
-- | ## World の記録
-- |
-- | Sedimented と Rejected は適用された World を記録する。
-- | これにより、どの法の下で沈殿/棄却されたかを追跡できる。
data StagingOutcome
  = Sedimented SedimentId World  -- 正常に沈殿（適用された World を記録）
  | Abandoned                     -- ユーザーによる取り消し
  | Rejected World Reason         -- 判例：Cognition が崩落しなかった

derive instance eqStagingOutcome :: Eq StagingOutcome

instance showStagingOutcome :: Show StagingOutcome where
  show (Sedimented sid world) = "(Sedimented " <> show sid <> " " <> show world.nomosVersion <> ")"
  show Abandoned = "Abandoned"
  show (Rejected world reason) = "(Rejected " <> show world.nomosVersion <> " " <> show reason <> ")"

-- ============================================================
-- Presheaf
-- ============================================================

-- | Presheaf: 前層（ステージング環境）
-- |
-- | Site C 上の前層 P: C^op → Set を表現する。
-- | 各 Subject（Site の点）に対して、ステージングされた Intent の集合を保持。
-- |
-- | ```
-- | P(subject) = { staged intents for this subject }
-- | ```
-- |
-- | ## フィールド
-- |
-- | - id: ステージング ID
-- | - state: 進行状態（Pending / Processing / Completed）
-- | - stagedIntents: Subject ごとのステージングされた Intent
-- | - createdAt: 作成時刻
-- | - completedAt: 完了時刻（Completed 時に設定）
-- | - outcome: 結果（Completed 時に設定）
-- | - targetWorld: Intent が依拠する World（IntentContext の target）
-- | - preservedZippers: 異常実行時に保存された IntentZipper（Json エンコード）
type Presheaf =
  { id :: StagingId
  , state :: StagingState
  , stagedIntents :: Map SubjectId (Array Json)
  , createdAt :: Timestamp
  , completedAt :: Maybe Timestamp
  , outcome :: Maybe StagingOutcome  -- 完了時に設定
  , targetWorld :: World             -- Intent が依拠する World
  , preservedZippers :: Array Json   -- 異常実行時の IntentZipper 保存
  }

-- | 空の Presheaf を作成
-- |
-- | targetWorld は Intent が依拠する法的文脈を指定する。
-- | Sedimentation 時に Attractor の現在の World と比較され、
-- | Connection が検証される。
emptyPresheaf :: StagingId -> Timestamp -> World -> Presheaf
emptyPresheaf sid ts world =
  { id: sid
  , state: Pending
  , stagedIntents: Map.empty
  , createdAt: ts
  , completedAt: Nothing
  , outcome: Nothing
  , targetWorld: world
  , preservedZippers: []
  }

-- | Intent をステージング
-- |
-- | まだ層化されていない状態で Intent を蓄積する。
stage :: SubjectId -> Json -> Presheaf -> Presheaf
stage subjectId intent presheaf =
  let current = Map.lookup subjectId presheaf.stagedIntents
      updated = case current of
        Nothing -> [intent]
        Just existing -> existing <> [intent]
  in presheaf { stagedIntents = Map.insert subjectId updated presheaf.stagedIntents }

-- | Presheaf を完了状態にする
-- |
-- | Sedimentation の結果を記録する。
-- | outcome には以下のいずれかを設定：
-- | - Sedimented: 正常に沈殿
-- | - Abandoned: ユーザーによる取り消し
-- | - Rejected: 判例（Cognition が崩落しなかった）
complete :: Timestamp -> StagingOutcome -> Presheaf -> Presheaf
complete ts result presheaf = presheaf
  { state = Completed
  , completedAt = Just ts
  , outcome = Just result
  }

-- | 異常実行時の IntentZipper を保存
-- |
-- | 「実行とは忘却である」の原則により、正常実行時は Intent 構造は忘却される。
-- | しかし異常実行時は IntentZipper を保存し、以下を可能にする：
-- |
-- | - 実行途中の状態の検査（デバッグ）
-- | - 再実行の試行
-- | - 判例（Rejected）との対応付け
-- |
-- | IntentZipper は Json としてエンコードされて保存される。
-- | これにより、Presheaf の永続化（SQLite 等）が容易になる。
preserveZipper :: Json -> Presheaf -> Presheaf
preserveZipper zipper presheaf = presheaf
  { preservedZippers = presheaf.preservedZippers <> [zipper]
  }
