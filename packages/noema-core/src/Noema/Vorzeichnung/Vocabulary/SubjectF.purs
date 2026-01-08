-- | Noema Vocabulary: SubjectF（意志を持つ主体）
-- |
-- | Subject は意志を持つ主体。DO として実装され、能動的に Sediment を沈殿させる。
-- |
-- | ## 圏論的位置づけ
-- |
-- | SubjectF は Base 圏の操作を定義する Functor。
-- | 水平射（Subject 間通信）は RPC として実装される。
module Noema.Vorzeichnung.Vocabulary.SubjectF
  ( SubjectKind(..)
  , SubjectState
  , SubjectInit
  , SubjectPatch
  , IntentEnvelope
  , Receipt
  , SubjectF(..)
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Argonaut.Core (Json)
import Noema.Core.Locus (SubjectId, SedimentId, Timestamp)
import Noema.Core.World (World, IntentContext)

-- | Subject の種別
data SubjectKind
  = ContractParty    -- 契約主体（売主、買主など）
  | ThingHolder      -- Thing を包摂する Subject（倉庫、店舗など）
  | SystemAgent      -- システムエージェント（自動処理）

derive instance eqSubjectKind :: Eq SubjectKind

instance showSubjectKind :: Show SubjectKind where
  show ContractParty = "ContractParty"
  show ThingHolder = "ThingHolder"
  show SystemAgent = "SystemAgent"

-- | Subject の状態
type SubjectState =
  { id :: SubjectId
  , kind :: SubjectKind
  , world :: World
  , lastActivity :: Timestamp
  }

-- | Subject 初期化パラメータ
type SubjectInit =
  { kind :: SubjectKind
  , world :: World
  }

-- | Subject 更新パラメータ
type SubjectPatch =
  { world :: Maybe World
  }

-- | Intent の封筒
-- | Subject 間通信のペイロード
type IntentEnvelope =
  { body :: Json
  , context :: IntentContext
  , seal :: String  -- 正当性の証明（署名）
  }

-- | 受領証
type Receipt =
  { id :: String
  , timestamp :: Timestamp
  , accepted :: Boolean
  }

-- | SubjectF: 意志を持つ主体への操作
-- |
-- | Arrow Effects のため、入力 i と出力 o を持つ。
-- | i -> ... の形式で入力を受け取り、結果を o に変換する。
data SubjectF i o
  -- Subject の生成・照会
  = CreateSubject (i -> SubjectInit) (SubjectId -> o)
  | GetSubject SubjectId (i -> Unit) (SubjectState -> o)
  | GetSubjectsByKind SubjectKind (i -> Unit) (Array SubjectState -> o)

  -- Subject の状態変更
  | UpdateSubject SubjectId (i -> SubjectPatch) (SedimentId -> o)

  -- 水平射（Subject 間通信）
  | SendIntent SubjectId (i -> IntentEnvelope) (Receipt -> o)
  | ConfirmReceipt String (i -> Unit) (Unit -> o)

-- | Functor instance
-- | o の変換を継続に適用
instance functorSubjectF :: Functor (SubjectF i) where
  map f = case _ of
    CreateSubject init k -> CreateSubject init (f <<< k)
    GetSubject sid toUnit k -> GetSubject sid toUnit (f <<< k)
    GetSubjectsByKind kind toUnit k -> GetSubjectsByKind kind toUnit (f <<< k)
    UpdateSubject sid toPatch k -> UpdateSubject sid toPatch (f <<< k)
    SendIntent sid toEnv k -> SendIntent sid toEnv (f <<< k)
    ConfirmReceipt rid toUnit k -> ConfirmReceipt rid toUnit (f <<< k)
