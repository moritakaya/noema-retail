module Noema.Sedimentation.Seal where

import Prelude

-- | 封印: トランザクションの完了証明
-- | 意志が事実として沈殿した証
newtype Seal = Seal
  { success :: Boolean
  , version :: Int
  , hash :: String
  , timestamp :: Number
  }

derive instance eqSeal :: Eq Seal
