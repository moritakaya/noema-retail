-- | Noema Vocabulary: SubjectF（意志を持つ主体）
-- |
-- | Subject は意志を持つ主体。DO として実装され、能動的に Sediment を沈殿させる。
-- |
-- | ## 圏論的位置づけ
-- |
-- | SubjectF は Base 圏の操作を定義する Functor。
-- | 水平射（Subject 間通信）は RPC として実装される。
-- |
-- | ## 存在論的構造
-- |
-- | Subject は Thing を「包摂」する：
-- | - Thing.situs :: SubjectId で包摂関係を表現
-- | - Subject は World を保持し、Thing はその World で解釈される
-- | - Subject の削除は包摂する Thing の孤立を意味する
-- |
-- | ## SubjectKind
-- |
-- | - ContractParty: 契約主体（売主、買主など）
-- | - ThingHolder: Thing を包摂する Subject（倉庫、店舗など）
-- | - SystemAgent: システムエージェント（自動処理）
-- |
-- | ## Arrow 版との使い分け
-- |
-- | ```purescript
-- | -- ✅ Arrow版（分岐禁止、推奨）
-- | arrowIntent =
-- |   createSubject initData
-- |   >>> arrIntent (_.id)
-- |
-- | -- SubjectIntent は Intent (SubjectF Unit) の別名
-- | type SubjectIntent a b = Intent (SubjectF Unit) a b
-- | ```
module Noema.Vorzeichnung.Vocabulary.SubjectF
  ( -- * Types
    SubjectKind(..)
  , SubjectState
  , SubjectInit
  , SubjectPatch
  , IntentEnvelope
  , Receipt
    -- * Functor
  , SubjectF(..)
    -- * Intent type
  , SubjectIntent
    -- * Smart constructors
  , createSubject
  , getSubject
  , getSubjectsByKind
  , updateSubject
  , sendIntent
  , confirmReceipt
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Argonaut.Core (Json)
import Noema.Topos.Situs (SubjectId, SedimentId, Timestamp)
import Noema.Topos.Nomos (World, IntentContext)
import Noema.Vorzeichnung.Intent (Intent, liftEffect)
import Noema.Vorzeichnung.Situierung (class Situable, PartitionKey(..))

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
-- | Arrow Effects 対応の二項関手。
-- | i -> 入力型（入力変換関数の引数）
-- | o -> 出力型（継続の戻り値）
-- |
-- | NoemaF との整合性のため二項関手として定義。
-- | Constructors.purs で `identity` を使って持ち上げる。
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

-- | Functor instance（o に対して）
instance functorSubjectF :: Functor (SubjectF i) where
  map f = case _ of
    CreateSubject toInit k -> CreateSubject toInit (f <<< k)
    GetSubject sid toUnit k -> GetSubject sid toUnit (f <<< k)
    GetSubjectsByKind kind toUnit k -> GetSubjectsByKind kind toUnit (f <<< k)
    UpdateSubject sid toPatch k -> UpdateSubject sid toPatch (f <<< k)
    SendIntent sid toEnv k -> SendIntent sid toEnv (f <<< k)
    ConfirmReceipt rid toUnit k -> ConfirmReceipt rid toUnit (f <<< k)

-- ============================================================
-- Intent 型
-- ============================================================

-- | Subject 操作の Intent
-- |
-- | `SubjectF Unit` を関手として使用。
-- | 入力型は Unit で固定され、Arrow の入力は Intent レベルで処理。
type SubjectIntent a b = Intent (SubjectF Unit) a b

-- ============================================================
-- スマートコンストラクタ
-- ============================================================

-- | Subject を作成する Intent
-- |
-- | ```purescript
-- | createSubject { kind: ThingHolder, world: someWorld }
-- |   :: SubjectIntent Unit SubjectId
-- | ```
createSubject :: SubjectInit -> SubjectIntent Unit SubjectId
createSubject init = liftEffect (CreateSubject (\_ -> init) identity)

-- | Subject を取得する Intent
-- |
-- | ```purescript
-- | getSubject (mkSubjectId "subject-001")
-- |   :: SubjectIntent Unit SubjectState
-- | ```
getSubject :: SubjectId -> SubjectIntent Unit SubjectState
getSubject sid = liftEffect (GetSubject sid (\_ -> unit) identity)

-- | 種別で Subject 一覧を取得する Intent
-- |
-- | ```purescript
-- | getSubjectsByKind ThingHolder
-- |   :: SubjectIntent Unit (Array SubjectState)
-- | ```
getSubjectsByKind :: SubjectKind -> SubjectIntent Unit (Array SubjectState)
getSubjectsByKind kind = liftEffect (GetSubjectsByKind kind (\_ -> unit) identity)

-- | Subject を更新する Intent
-- |
-- | ```purescript
-- | updateSubject sid { world: Just newWorld }
-- |   :: SubjectIntent Unit SedimentId
-- | ```
updateSubject :: SubjectId -> SubjectPatch -> SubjectIntent Unit SedimentId
updateSubject sid patch = liftEffect (UpdateSubject sid (\_ -> patch) identity)

-- | 他の Subject へ Intent を送信（水平射）
-- |
-- | ```purescript
-- | sendIntent targetSid envelope
-- |   :: SubjectIntent Unit Receipt
-- | ```
sendIntent :: SubjectId -> IntentEnvelope -> SubjectIntent Unit Receipt
sendIntent targetSid envelope = liftEffect (SendIntent targetSid (\_ -> envelope) identity)

-- | Receipt を確認
-- |
-- | ```purescript
-- | confirmReceipt "receipt-001"
-- |   :: SubjectIntent Unit Unit
-- | ```
confirmReceipt :: String -> SubjectIntent Unit Unit
confirmReceipt rid = liftEffect (ConfirmReceipt rid (\_ -> unit) identity)

-- ============================================================
-- Situable インスタンス
-- ============================================================

-- | SubjectF (Unit) の Situable インスタンス
-- |
-- | Subject 操作のルーティング先を決定する。
-- | - 特定の Subject への操作 → BySubject
-- | - 種別検索など複数対象 → Broadcast
instance situableSubjectFUnit :: Situable (SubjectF Unit) where
  situate = case _ of
    CreateSubject _ _ -> Broadcast  -- 新規作成先は動的に決定
    GetSubject sid _ _ -> BySubject sid
    GetSubjectsByKind _ _ _ -> Broadcast  -- 複数 Subject を検索
    UpdateSubject sid _ _ -> BySubject sid
    SendIntent targetSid _ _ -> BySubject targetSid
    ConfirmReceipt _ _ _ -> Broadcast  -- Receipt ID から Subject を特定できない
