-- | Noema Cognition: SubjectInterpretation
-- |
-- | SubjectF（主体操作語彙）を Factum（事実）へ解釈する。
-- |
-- | ## 役割
-- |
-- | - CreateSubject, GetSubject 等の主体操作を SQLite 操作に変換
-- | - FFI 境界で Effect を Factum に認識（recognize）
-- | - Subject 間通信（水平射）のスタブ実装
-- |
-- | ## 圏論的解釈
-- |
-- | Interpretation は A-algebra homomorphism として機能:
-- | - SubjectF は主体操作の Functor
-- | - Interpretation は Intent（意志構造）を忘却し、
-- |   SQLite の状態変更という事実へ崩落させる
-- |
-- | > 実行とは忘却である。
-- |
-- | ## Subject の存在論的位置づけ
-- |
-- | Subject は意志を持つ主体。Thing を「包摂」する。
-- | - Subject.world: 法座標（Nomos バージョン）
-- | - Thing.situs: 包摂する Subject の ID
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | env <- recognize $ mkSubjectEnv sql
-- | result <- runSubjectIntent env (getSubject sid) unit
-- | -- result :: Factum SubjectState
-- | ```
module Noema.Cognition.SubjectInterpretation
  ( runSubjectIntent
  , SubjectEnv
  , mkSubjectEnv
  , initializeSubjectSchema
  , interpretSubjectF
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign, unsafeFromForeign)

import Noema.Topos.Situs
  ( currentTimestamp
  , SubjectId
  , SedimentId(..)
  , Timestamp(..)
  , mkSubjectId
  , mkSedimentId
  , unwrapSubjectId
  )
import Noema.Topos.Nomos
  ( World
  , NomosVersion(..)
  , mkWorld
  )
import Noema.Vorzeichnung.Vocabulary.SubjectF
  ( SubjectF(..)
  , SubjectKind(..)
  , SubjectState
  , SubjectIntent
  , Receipt
  )
import Noema.Cognition.Interpretation (Interpretation, runInterpretation)
import Noema.Sedimentation.Factum (Factum, recognize)
import Platform.Cloudflare.FFI.SqlStorage (SqlStorage)

-- Import from InventoryInterpretation (shared FFI)
import Noema.Cognition.InventoryInterpretation (Cursor, exec, execWithParams, one, toArray, getField, generateId)

-- ============================================================
-- 環境
-- ============================================================

-- | Subject Interpretation 環境
-- |
-- | SQLite Storage への参照を保持する。
type SubjectEnv =
  { sql :: SqlStorage
  }

-- | 環境を作成
mkSubjectEnv :: SqlStorage -> SubjectEnv
mkSubjectEnv sql = { sql }

-- ============================================================
-- スキーマ初期化
-- ============================================================

-- | Subject スキーマを初期化
-- |
-- | Durable Object の初回アクセス時に呼び出す。
initializeSubjectSchema :: SqlStorage -> Effect Unit
initializeSubjectSchema sql = do
  -- Subject テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS subject (
      id TEXT PRIMARY KEY,
      kind TEXT NOT NULL,
      nomos_version TEXT NOT NULL,
      region TEXT,
      world_timestamp REAL NOT NULL,
      last_activity REAL NOT NULL,
      created_at REAL NOT NULL
    )
  """

  -- Subject イベントログ
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS subject_log (
      id TEXT PRIMARY KEY,
      subject_id TEXT NOT NULL,
      event_type TEXT NOT NULL,
      payload TEXT,
      created_at REAL NOT NULL,
      FOREIGN KEY (subject_id) REFERENCES subject(id)
    )
  """

  -- インデックス
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_subject_kind ON subject(kind)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_subject_log_created ON subject_log(created_at)"

  pure unit

-- ============================================================
-- Interpretation 実装
-- ============================================================

-- | SubjectF を Factum に解釈する Interpretation
-- |
-- | 圏論的解釈:
-- | この関数は自然変換 SubjectF ~> Factum を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な SQLite 実装へ変換する。
interpretSubjectF :: SubjectEnv -> Interpretation (SubjectF Unit)
interpretSubjectF env = case _ of
  CreateSubject toInit k -> do
    let init = toInit unit
    now <- recognize currentTimestamp
    newId <- recognize generateId

    -- Subject を INSERT
    let _ = execWithParams env.sql
          """
          INSERT INTO subject (id, kind, nomos_version, region, world_timestamp, last_activity, created_at)
          VALUES (?, ?, ?, ?, ?, ?, ?)
          """
          [ unsafeToForeign newId
          , unsafeToForeign (showSubjectKind init.kind)
          , unsafeToForeign (unwrapNomosVersion init.world.nomosVersion)
          , unsafeToForeign (maybeToForeign init.world.region)
          , unsafeToForeign (unwrap init.world.timestamp)
          , unsafeToForeign (unwrap now)
          , unsafeToForeign (unwrap now)
          ]

    -- ログを記録
    logId <- recognize generateId
    let _ = execWithParams env.sql
          """
          INSERT INTO subject_log (id, subject_id, event_type, payload, created_at)
          VALUES (?, ?, 'created', NULL, ?)
          """
          [ unsafeToForeign logId
          , unsafeToForeign newId
          , unsafeToForeign (unwrap now)
          ]

    pure (k (mkSubjectId newId))

  GetSubject sid _toUnit k -> do
    let sidStr = unwrapSubjectId sid
    let cursor = execWithParams env.sql
          "SELECT * FROM subject WHERE id = ?"
          [ unsafeToForeign sidStr ]

    let maybeRow = one cursor
    let state = case maybeRow of
          Nothing -> defaultSubjectState sid
          Just row -> rowToSubjectState row

    pure (k state)

  GetSubjectsByKind kind _toUnit k -> do
    let kindStr = showSubjectKind kind
    let cursor = execWithParams env.sql
          "SELECT * FROM subject WHERE kind = ?"
          [ unsafeToForeign kindStr ]

    let rows = toArray cursor
    let states = map rowToSubjectState rows

    pure (k states)

  UpdateSubject sid toPatch k -> do
    let patch = toPatch unit
    now <- recognize currentTimestamp
    let sidStr = unwrapSubjectId sid

    -- World の更新（patch.world が Just の場合のみ）
    case patch.world of
      Nothing -> pure unit
      Just newWorld -> do
        let _ = execWithParams env.sql
              """
              UPDATE subject
              SET nomos_version = ?, region = ?, world_timestamp = ?, last_activity = ?
              WHERE id = ?
              """
              [ unsafeToForeign (unwrapNomosVersion newWorld.nomosVersion)
              , unsafeToForeign (maybeToForeign newWorld.region)
              , unsafeToForeign (unwrap newWorld.timestamp)
              , unsafeToForeign (unwrap now)
              , unsafeToForeign sidStr
              ]
        pure unit

    -- ログを記録
    logId <- recognize generateId
    let _ = execWithParams env.sql
          """
          INSERT INTO subject_log (id, subject_id, event_type, payload, created_at)
          VALUES (?, ?, 'updated', NULL, ?)
          """
          [ unsafeToForeign logId
          , unsafeToForeign sidStr
          , unsafeToForeign (unwrap now)
          ]

    -- SedimentId を生成
    let sedimentId = mkSedimentId 1  -- TODO: Lamport Clock

    pure (k sedimentId)

  -- 水平射（Subject 間通信）- スタブ実装
  SendIntent _targetSid toEnv k -> do
    let _envelope = toEnv unit
    now <- recognize currentTimestamp

    -- TODO: DO RPC 実装
    -- 現在はスタブとして成功を返す
    receiptId <- recognize generateId
    let receipt :: Receipt
        receipt =
          { id: receiptId
          , timestamp: now
          , accepted: true
          }

    pure (k receipt)

  ConfirmReceipt _receiptId _toUnit k -> do
    -- TODO: Receipt 確認ロジック
    pure (k unit)

-- ============================================================
-- Intent 実行
-- ============================================================

-- | SubjectIntent を Factum で実行
-- |
-- | Arrow 版では入力値を明示的に渡す必要がある。
-- |
-- | 使用例:
-- | ```purescript
-- | result <- runSubjectIntent env (getSubject sid) unit
-- | -- result :: Factum SubjectState
-- |
-- | -- エントリーポイントで Factum → Effect に変換
-- | handleFetch req = collapse do
-- |   result <- runSubjectIntent env intent unit
-- |   ...
-- | ```
runSubjectIntent :: forall a b. SubjectEnv -> SubjectIntent a b -> a -> Factum b
runSubjectIntent env intent input =
  runInterpretation (interpretSubjectF env) intent input

-- ============================================================
-- ヘルパー関数
-- ============================================================

-- | SubjectKind を文字列に変換
showSubjectKind :: SubjectKind -> String
showSubjectKind = case _ of
  ContractParty -> "contract_party"
  ThingHolder -> "thing_holder"
  SystemAgent -> "system_agent"

-- | 文字列を SubjectKind に変換
parseSubjectKind :: String -> SubjectKind
parseSubjectKind = case _ of
  "contract_party" -> ContractParty
  "thing_holder" -> ThingHolder
  "system_agent" -> SystemAgent
  _ -> ThingHolder  -- デフォルト

-- | NomosVersion を unwrap
unwrapNomosVersion :: NomosVersion -> String
unwrapNomosVersion (NomosVersion v) = v

-- | Maybe を Foreign に変換（null 対応）
maybeToForeign :: forall a. Maybe a -> Foreign
maybeToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)  -- NULL として扱う
  Just a -> unsafeToForeign a

-- | デフォルトの SubjectState
defaultSubjectState :: SubjectId -> SubjectState
defaultSubjectState sid =
  { id: sid
  , kind: ThingHolder
  , world: mkWorld (NomosVersion "0.0.0") (Timestamp 0.0)
  , lastActivity: Timestamp 0.0
  }

-- | 行データを SubjectState に変換
rowToSubjectState :: Foreign -> SubjectState
rowToSubjectState row =
  let
    sid = mkSubjectId (unsafeFromForeign (getField row "id"))
    kindStr = unsafeFromForeign (getField row "kind") :: String
    nomosVersion = NomosVersion (unsafeFromForeign (getField row "nomos_version"))
    worldTs = Timestamp (unsafeFromForeign (getField row "world_timestamp"))
    lastActivity = Timestamp (unsafeFromForeign (getField row "last_activity"))
  in
    { id: sid
    , kind: parseSubjectKind kindStr
    , world: mkWorld nomosVersion worldTs
    , lastActivity: lastActivity
    }
