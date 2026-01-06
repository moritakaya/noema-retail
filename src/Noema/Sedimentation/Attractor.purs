module Noema.Sedimentation.Attractor where

import Prelude
import Noema.Sedimentation.Seal (Seal)

-- | Attractor: 意志が沈殿する引き込み域
-- | 力学系における安定点
-- | 具体的な実装は Platform/ で提供
class Attractor a where
  -- | 意志を事実として沈殿させる
  sediment :: forall intent. intent -> a Seal
