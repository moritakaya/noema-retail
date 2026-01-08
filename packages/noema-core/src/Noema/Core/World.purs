-- | Noema Core: World（法座標）
-- |
-- | Nomos のバージョンと適用文脈を定義する。
-- |
-- | ## 圏論的位置づけ
-- |
-- | World は Fiber 圏の解釈を規定する。
-- | Nomos（大域意志）が Sediment の解釈を規定し、
-- | DO が眠って起きた時に World が変わりうる（コードのデプロイ）。
module Noema.Core.World
  ( NomosVersion(..)
  , NomosReference(..)
  , World
  , IntentContext
  , mkWorld
  , mkIntentContext
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Noema.Core.Locus (Timestamp)

-- | Nomos のバージョン
-- | セマンティックバージョニングを想定
newtype NomosVersion = NomosVersion String

derive instance eqNomosVersion :: Eq NomosVersion
derive instance ordNomosVersion :: Ord NomosVersion
derive newtype instance showNomosVersion :: Show NomosVersion

-- | Nomos への参照（契約が依拠する法）
type NomosReference =
  { version :: NomosVersion
  , jurisdiction :: Maybe String  -- 法域（日本法、米国法など）
  , customTerms :: Maybe String   -- カスタム条項への参照
  }

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
