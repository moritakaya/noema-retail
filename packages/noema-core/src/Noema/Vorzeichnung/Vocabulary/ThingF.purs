-- | Noema Vocabulary: ThingF（意志を持たない物）
-- |
-- | Thing は意志を持たない物。Subject に包摂され、
-- | Subject^op → Set として観測される。
-- |
-- | ## 圏論的位置づけ
-- |
-- | ThingF は Fiber 圏の操作を定義する Functor。
-- | Thing の同一性は包摂する Subject の id で決まる。
-- |
-- | ## 時間構造（Husserl）
-- |
-- | - Retention（把持）: 過去の Snapshot
-- | - Primal（原印象）: 現在の状態
-- | - Protention（予持）: 未来の Pending Intent
module Noema.Vorzeichnung.Vocabulary.ThingF
  ( -- * 型定義
    PropertyKey(..)
  , PropertyValue
  , TimeRange
  , ChangeReason(..)
  , SitusChange
  , PendingIntent
  , ProtentionId(..)
  , ThingSnapshot
  , ThingState
  , Sediment
  , ThingF(..)
    -- * Intent 型
  , ThingIntent
    -- * ChangeReason ヘルパー（ドメイン非依存）
  , mkChangeReason
  , getReasonType
  , getReasonDetail
  , getReasonContractId
  , transferReason
    -- * スマートコンストラクタ（属性）
  , getProperty
  , setProperty
    -- * スマートコンストラクタ（位置）
  , getSitus
  , recordSitusChange
    -- * スマートコンストラクタ（時間 - Retention）
  , getRetention
  , getRetentionRange
    -- * スマートコンストラクタ（時間 - Primal）
  , getPrimal
    -- * スマートコンストラクタ（時間 - Protention）
  , registerProtention
  , getProtentions
  , realizeProtention
  , cancelProtention
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Data.Map (Map)
import Data.Newtype (class Newtype)
import Data.Argonaut.Core (Json, jsonNull, stringify, caseJsonObject, toObject, fromObject, fromString, toString)
import Data.Argonaut.Encode (encodeJson)
import Foreign.Object as Object
import Noema.Topos.Situs (ThingId, SubjectId, SedimentId, Timestamp, ContractId, mkContractId, unwrapContractId)
import Noema.Vorzeichnung.Intent (Intent, liftEffect)

-- | Property のキー
newtype PropertyKey = PropertyKey String

derive instance eqPropertyKey :: Eq PropertyKey
derive instance ordPropertyKey :: Ord PropertyKey
derive newtype instance showPropertyKey :: Show PropertyKey

-- | Property の値（任意の JSON）
type PropertyValue = Json

-- | 時間範囲
type TimeRange =
  { from :: Timestamp
  , to :: Timestamp
  }

-- | 位置変更の理由（ドメイン非依存）
-- |
-- | Json として格納され、各ドメインで解釈される。
-- | noema-retail では RetailChangeReason への変換を提供。
-- |
-- | ## 構造
-- |
-- | ```json
-- | { "type": "transfer", "detail": null, "contractId": null }
-- | { "type": "sale", "detail": null, "contractId": "contract-123" }
-- | ```
newtype ChangeReason = ChangeReason Json

derive instance eqChangeReason :: Eq ChangeReason
derive instance newtypeChangeReason :: Newtype ChangeReason _

instance showChangeReason :: Show ChangeReason where
  show (ChangeReason json) = "(ChangeReason " <> stringify json <> ")"

-- | ChangeReason を作成
-- |
-- | reasonType と detail、contractId を指定して作成する。
-- | 各ドメインはこの関数を使って具体的な理由を構築する。
mkChangeReason :: String -> Maybe String -> Maybe ContractId -> ChangeReason
mkChangeReason reasonType detail contractRef =
  ChangeReason $ fromObject $ Object.fromFoldable
    [ "type" /\ fromString reasonType
    , "detail" /\ case detail of
        Just d -> fromString d
        Nothing -> jsonNull
    , "contractId" /\ case contractRef of
        Just cid -> fromString (unwrapContractId cid)
        Nothing -> jsonNull
    ]

-- | ChangeReason から type を取得
getReasonType :: ChangeReason -> String
getReasonType (ChangeReason json) =
  caseJsonObject "unknown" extractType json
  where
    extractType obj = case Object.lookup "type" obj >>= toString of
      Just t -> t
      Nothing -> "unknown"

-- | ChangeReason から detail を取得
getReasonDetail :: ChangeReason -> Maybe String
getReasonDetail (ChangeReason json) =
  case toObject json of
    Just obj -> Object.lookup "detail" obj >>= toString
    Nothing -> Nothing

-- | ChangeReason から contractId を取得
getReasonContractId :: ChangeReason -> Maybe ContractId
getReasonContractId (ChangeReason json) =
  case toObject json of
    Just obj -> Object.lookup "contractId" obj >>= toString >>= \s -> Just (mkContractId s)
    Nothing -> Nothing

-- | 内部移動用の定義済み ChangeReason
-- |
-- | ドメイン非依存の「移動」を表す。
transferReason :: ChangeReason
transferReason = mkChangeReason "transfer" Nothing Nothing

-- | 位置変更の記録
-- | ※ Situs = Topos/Situs モジュールとの一貫性のため locus から改名
type SitusChange =
  { from :: SubjectId
  , to :: SubjectId
  , reason :: ChangeReason
  , contractRef :: Maybe ContractId
  }

-- | Pending Intent（予持）
-- | 未来に実行される予定の Intent
type PendingIntent =
  { scheduledAt :: Timestamp
  , intentBody :: Json
  , condition :: Maybe String  -- 条件（オプション）
  }

-- | Protention の識別子
newtype ProtentionId = ProtentionId String

derive instance eqProtentionId :: Eq ProtentionId
derive instance ordProtentionId :: Ord ProtentionId
derive newtype instance showProtentionId :: Show ProtentionId

-- | Thing の Snapshot（過去の把持）
-- | ある時点での Thing の完全な状態
type ThingSnapshot =
  { thingId :: ThingId
  , timestamp :: Timestamp
  , properties :: Map PropertyKey PropertyValue
  , situs :: SubjectId  -- 包摂する Subject（位置）
  , sedimentId :: SedimentId
  }

-- | Thing の現在状態（原印象）
type ThingState =
  { thingId :: ThingId
  , properties :: Map PropertyKey PropertyValue
  , situs :: SubjectId  -- 包摂する Subject（位置）
  , lastModified :: Timestamp
  , protentions :: Array ProtentionId
  }

-- | Sediment レコード
-- | 状態変更の不変記録（INSERT のみ、UPDATE 禁止）
type Sediment =
  { sequenceId :: Int
  , intentType :: String
  , payload :: Json
  , createdAt :: Timestamp
  }

-- | ThingF: もの・ことへの操作
-- |
-- | 時間構造（Husserl）に基づく三層：
-- | - Retention: 過去の把持（Snapshot）
-- | - Primal: 現在（最新の Sediment 積分値）
-- | - Protention: 未来の予持（Alarm と連動）
data ThingF i o
  -- === 属性 (Property) ===
  = GetProperty ThingId PropertyKey (i -> Unit) (PropertyValue -> o)
  | SetProperty ThingId PropertyKey (i -> PropertyValue) (SedimentId -> o)

  -- === 位置 (Situs) ===
  | GetSitus ThingId (i -> Unit) (SubjectId -> o)
  | RecordSitusChange ThingId (i -> SitusChange) (SedimentId -> o)

  -- === 時間 (Temporality) ===

  -- Retention: 過去の把持
  | GetRetention ThingId Timestamp (i -> Unit) (ThingSnapshot -> o)
  | GetRetentionRange ThingId TimeRange (i -> Unit) (Array Sediment -> o)

  -- Primal: 現在
  | GetPrimal ThingId (i -> Unit) (ThingState -> o)

  -- Protention: 未来の予持
  | RegisterProtention ThingId (i -> PendingIntent) (ProtentionId -> o)
  | GetProtentions ThingId (i -> Unit) (Array PendingIntent -> o)
  | RealizeProtention ProtentionId (i -> Unit) (SedimentId -> o)
  | CancelProtention ProtentionId (i -> Unit) (Unit -> o)

-- | Functor instance
instance functorThingF :: Functor (ThingF i) where
  map f = case _ of
    GetProperty tid key toUnit k -> GetProperty tid key toUnit (f <<< k)
    SetProperty tid key toVal k -> SetProperty tid key toVal (f <<< k)
    GetSitus tid toUnit k -> GetSitus tid toUnit (f <<< k)
    RecordSitusChange tid toChange k -> RecordSitusChange tid toChange (f <<< k)
    GetRetention tid ts toUnit k -> GetRetention tid ts toUnit (f <<< k)
    GetRetentionRange tid range toUnit k -> GetRetentionRange tid range toUnit (f <<< k)
    GetPrimal tid toUnit k -> GetPrimal tid toUnit (f <<< k)
    RegisterProtention tid toPending k -> RegisterProtention tid toPending (f <<< k)
    GetProtentions tid toUnit k -> GetProtentions tid toUnit (f <<< k)
    RealizeProtention pid toUnit k -> RealizeProtention pid toUnit (f <<< k)
    CancelProtention pid toUnit k -> CancelProtention pid toUnit (f <<< k)

-- ============================================================
-- Intent 型
-- ============================================================

-- | ThingIntent: Thing 操作の Intent
-- |
-- | Arrow-based Intent で Thing 操作を表現する。
-- | 分岐禁止（ArrowChoice なし）により、静的な操作列を保証。
type ThingIntent a b = Intent (ThingF Unit) a b

-- ============================================================
-- スマートコンストラクタ
-- ============================================================

-- | 属性を取得
-- |
-- | ```purescript
-- | intent :: ThingIntent Unit PropertyValue
-- | intent = getProperty tid (PropertyKey "sku")
-- | ```
getProperty :: ThingId -> PropertyKey -> ThingIntent Unit PropertyValue
getProperty tid key = liftEffect (GetProperty tid key (\_ -> unit) identity)

-- | 属性を設定
-- |
-- | ```purescript
-- | intent :: ThingIntent Unit SedimentId
-- | intent = setProperty tid (PropertyKey "color") (encodeJson "red")
-- | ```
setProperty :: ThingId -> PropertyKey -> PropertyValue -> ThingIntent Unit SedimentId
setProperty tid key value = liftEffect (SetProperty tid key (\_ -> value) identity)

-- | 位置（Situs）を取得
-- |
-- | Thing を包摂する Subject の ID を返す。
getSitus :: ThingId -> ThingIntent Unit SubjectId
getSitus tid = liftEffect (GetSitus tid (\_ -> unit) identity)

-- | 位置変更を記録
-- |
-- | Situs の変更履歴を Sediment として記録する。
recordSitusChange :: ThingId -> SitusChange -> ThingIntent Unit SedimentId
recordSitusChange tid change = liftEffect (RecordSitusChange tid (\_ -> change) identity)

-- | 過去の Snapshot を取得（Retention）
-- |
-- | 指定時点での Thing の状態を復元する。
getRetention :: ThingId -> Timestamp -> ThingIntent Unit ThingSnapshot
getRetention tid ts = liftEffect (GetRetention tid ts (\_ -> unit) identity)

-- | 期間内の Sediment を取得（Retention）
-- |
-- | 指定期間のすべての Sediment を時系列で返す。
getRetentionRange :: ThingId -> TimeRange -> ThingIntent Unit (Array Sediment)
getRetentionRange tid range = liftEffect (GetRetentionRange tid range (\_ -> unit) identity)

-- | 現在の状態を取得（Primal）
-- |
-- | Sediment の積分値としての現在状態を返す。
getPrimal :: ThingId -> ThingIntent Unit ThingState
getPrimal tid = liftEffect (GetPrimal tid (\_ -> unit) identity)

-- | Protention を登録（予持）
-- |
-- | 未来に実行される予定の Intent を登録する。
-- | Alarm と連動して指定時刻に実行される。
registerProtention :: ThingId -> PendingIntent -> ThingIntent Unit ProtentionId
registerProtention tid pending = liftEffect (RegisterProtention tid (\_ -> pending) identity)

-- | Protention 一覧を取得
-- |
-- | 登録済みの Pending Intent を返す。
getProtentions :: ThingId -> ThingIntent Unit (Array PendingIntent)
getProtentions tid = liftEffect (GetProtentions tid (\_ -> unit) identity)

-- | Protention を実現（完了）
-- |
-- | Pending Intent を実行済みとしてマークする。
realizeProtention :: ProtentionId -> ThingIntent Unit SedimentId
realizeProtention pid = liftEffect (RealizeProtention pid (\_ -> unit) identity)

-- | Protention をキャンセル
-- |
-- | 予定された Intent をキャンセルする。
cancelProtention :: ProtentionId -> ThingIntent Unit Unit
cancelProtention pid = liftEffect (CancelProtention pid (\_ -> unit) identity)
