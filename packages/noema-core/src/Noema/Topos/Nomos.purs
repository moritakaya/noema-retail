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
module Noema.Topos.Nomos
  ( NomosVersion(..)
  , NomosReference(..)
  , World
  , IntentContext
  , mkWorld
  , mkIntentContext
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Noema.Topos.Situs (Timestamp)

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
