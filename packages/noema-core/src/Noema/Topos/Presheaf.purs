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
module Noema.Topos.Presheaf
  ( Presheaf(..)
  , StagingId(..)
  , StagingState(..)
  , mkStagingId
  , emptyPresheaf
  , stage
  , commit
  , rollback
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Argonaut.Core (Json)
import Noema.Topos.Situs (Timestamp, SubjectId)

-- | ステージング ID
newtype StagingId = StagingId String

derive instance eqStagingId :: Eq StagingId
derive instance ordStagingId :: Ord StagingId
derive newtype instance showStagingId :: Show StagingId

mkStagingId :: String -> StagingId
mkStagingId = StagingId

-- | ステージングの状態
data StagingState
  = Pending       -- 保留中
  | Committed     -- コミット済み
  | RolledBack    -- ロールバック済み

derive instance eqStagingState :: Eq StagingState

instance showStagingState :: Show StagingState where
  show Pending = "Pending"
  show Committed = "Committed"
  show RolledBack = "RolledBack"

-- | Presheaf: 前層（ステージング環境）
-- |
-- | Site C 上の前層 P: C^op → Set を表現する。
-- | 各 Subject（Site の点）に対して、ステージングされた Intent の集合を保持。
-- |
-- | ```
-- | P(subject) = { staged intents for this subject }
-- | ```
type Presheaf =
  { id :: StagingId
  , state :: StagingState
  , stagedIntents :: Map SubjectId (Array Json)
  , createdAt :: Timestamp
  , committedAt :: Maybe Timestamp
  }

-- | 空の Presheaf を作成
emptyPresheaf :: StagingId -> Timestamp -> Presheaf
emptyPresheaf sid ts =
  { id: sid
  , state: Pending
  , stagedIntents: Map.empty
  , createdAt: ts
  , committedAt: Nothing
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

-- | Presheaf をコミット（層化の開始）
-- |
-- | Sedimentation へ渡す準備が完了したことを示す。
commit :: Timestamp -> Presheaf -> Presheaf
commit ts presheaf = presheaf
  { state = Committed
  , committedAt = Just ts
  }

-- | Presheaf をロールバック
-- |
-- | ステージングされた Intent を破棄する。
rollback :: Presheaf -> Presheaf
rollback presheaf = presheaf
  { state = RolledBack
  , stagedIntents = Map.empty
  }
