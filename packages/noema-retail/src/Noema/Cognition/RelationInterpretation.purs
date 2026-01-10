-- | Noema Cognition: RelationInterpretation
-- |
-- | RelationF（関係性語彙）を Factum（事実）へ解釈する。
-- |
-- | ## 役割
-- |
-- | - GetRelation, AddRelation 等の関係操作を SQLite 操作に変換
-- | - Subject-Thing 間の関係（所有、占有、引当など）を管理
-- | - 所有権移転の経路を記録
-- |
-- | ## 圏論的解釈
-- |
-- | Interpretation は A-algebra homomorphism として機能:
-- | - RelationF は関係操作の Functor（Span 圏の操作）
-- | - Interpretation は Intent（意志構造）を忘却し、
-- |   SQLite の状態変更という事実へ崩落させる
-- |
-- | > 実行とは忘却である。
-- |
-- | ## 関係の存在論的位置づけ
-- |
-- | 関係は Subject-Thing 間の射として表現される。
-- | - Source of Truth: Thing を包摂する Subject が保持
-- | - Container の Contents: View（キャッシュ）
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | env <- recognize $ mkRelationEnv sql
-- | result <- runRelationIntent env (getRelationsFrom subjectId Owns) unit
-- | -- result :: Factum (Array Relation)
-- | ```
module Noema.Cognition.RelationInterpretation
  ( realizeRelationIntent
  , RelationEnv
  , mkRelationEnv
  , initializeRelationSchema
  , interpretRelationF
  ) where

import Prelude

import Data.Array as Array
import Data.Argonaut.Core (Json, stringify, jsonNull)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign, unsafeFromForeign)

import Noema.Topos.Situs
  ( SubjectId
  , ThingId
  , RelationId
  , SedimentId
  , Timestamp(..)
  , ContractId
  , Quantity
  , currentTimestamp
  , mkSubjectId
  , mkThingId
  , mkRelationId
  , mkSedimentId
  , mkQuantity
  , unwrapSubjectId
  , unwrapThingId
  , unwrapRelationId
  )
import Noema.Vorzeichnung.Vocabulary.RelationF
  ( RelationF(..)
  , RelationKind(..)
  , RelationMetadata(..)
  , SecurityType(..)
  , AgencyScope(..)
  , ChangeType(..)
  , ConditionType(..)
  , Relation
  , RelationInit
  , OwnershipTransfer
  , ObserverContext
  , ThingView
  , IntentionView
  )
import Noema.Vorzeichnung.Intent (Intent)
import Noema.Cognition.Interpretation (Interpretation, realizeInterpretation)
import Noema.Sedimentation.Factum (Factum, recognize)
import Platform.Cloudflare.FFI.SqlStorage (SqlStorage)

-- Import from InventoryInterpretation (shared FFI)
import Noema.Cognition.InventoryInterpretation (Cursor, exec, execWithParams, one, toArray, getField, generateId)

-- ============================================================
-- 環境
-- ============================================================

-- | Relation Interpretation 環境
-- |
-- | SQLite Storage への参照を保持する。
type RelationEnv =
  { sql :: SqlStorage
  }

-- | 環境を作成
mkRelationEnv :: SqlStorage -> RelationEnv
mkRelationEnv sql = { sql }

-- ============================================================
-- スキーマ初期化
-- ============================================================

-- | Relation スキーマを初期化
-- |
-- | SubjectAttractor の初回アクセス時に呼び出す。
-- | 関係は Subject に属するため、SubjectAttractor 内で管理。
initializeRelationSchema :: SqlStorage -> Effect Unit
initializeRelationSchema sql = do
  -- Relation テーブル（関係マスタ）
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS relation (
      id TEXT PRIMARY KEY,
      kind TEXT NOT NULL,
      from_subject TEXT NOT NULL,
      to_thing TEXT NOT NULL,
      metadata TEXT,
      valid_from REAL NOT NULL,
      valid_until REAL,
      contract_ref TEXT,
      created_at REAL NOT NULL,
      removed_at REAL,
      FOREIGN KEY (from_subject) REFERENCES subject(id)
    )
  """

  -- 所有権移転ログ（INSERT のみ、経路を記録）
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS ownership_transfer_log (
      id TEXT PRIMARY KEY,
      thing_id TEXT NOT NULL,
      from_subject TEXT NOT NULL,
      to_subject TEXT NOT NULL,
      via_subject TEXT,
      contract_ref TEXT NOT NULL,
      created_at REAL NOT NULL
    )
  """

  -- 関係 Sediment ログ（INSERT のみ）
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS relation_sediment (
      id TEXT PRIMARY KEY,
      relation_id TEXT NOT NULL,
      sequence_id INTEGER NOT NULL,
      operation TEXT NOT NULL,
      payload TEXT NOT NULL,
      created_at REAL NOT NULL,
      FOREIGN KEY (relation_id) REFERENCES relation(id)
    )
  """

  -- インデックス
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_relation_from ON relation(from_subject, kind)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_relation_to ON relation(to_thing, kind)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_relation_kind ON relation(kind)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_relation_valid ON relation(valid_from, valid_until)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_ownership_transfer_thing ON ownership_transfer_log(thing_id)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_relation_removed ON relation(removed_at)"

  pure unit

-- ============================================================
-- Intent の型定義
-- ============================================================

-- | RelationIntent の型エイリアス
type RelationIntent a b = Intent (RelationF Unit) a b

-- ============================================================
-- Interpretation 実装
-- ============================================================

-- | RelationF を Factum に解釈する Interpretation
-- |
-- | 圏論的解釈:
-- | この関数は自然変換 RelationF ~> Factum を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な SQLite 実装へ変換する。
interpretRelationF :: RelationEnv -> Interpretation (RelationF Unit)
interpretRelationF env = case _ of
  -- === 照会系 ===

  GetRelation rid _toUnit k -> do
    let ridStr = unwrapRelationId rid
    let cursor = execWithParams env.sql
          """
          SELECT id, kind, from_subject, to_thing, metadata,
                 valid_from, valid_until, contract_ref, created_at
          FROM relation
          WHERE id = ? AND removed_at IS NULL
          """
          [ unsafeToForeign ridStr ]

    let maybeRow = one cursor
    let result = case maybeRow of
          Nothing -> Nothing
          Just row -> Just (rowToRelation row)

    pure (k result)

  GetRelationsFrom sid kind _toUnit k -> do
    let sidStr = unwrapSubjectId sid
    let kindStr = relationKindToString kind
    let cursor = execWithParams env.sql
          """
          SELECT id, kind, from_subject, to_thing, metadata,
                 valid_from, valid_until, contract_ref, created_at
          FROM relation
          WHERE from_subject = ? AND kind = ? AND removed_at IS NULL
          ORDER BY created_at DESC
          """
          [ unsafeToForeign sidStr
          , unsafeToForeign kindStr
          ]

    let rows = toArray cursor
    let relations = map rowToRelation rows

    pure (k relations)

  GetRelationsTo tid kind _toUnit k -> do
    let tidStr = unwrapThingId tid
    let kindStr = relationKindToString kind
    let cursor = execWithParams env.sql
          """
          SELECT id, kind, from_subject, to_thing, metadata,
                 valid_from, valid_until, contract_ref, created_at
          FROM relation
          WHERE to_thing = ? AND kind = ? AND removed_at IS NULL
          ORDER BY created_at DESC
          """
          [ unsafeToForeign tidStr
          , unsafeToForeign kindStr
          ]

    let rows = toArray cursor
    let relations = map rowToRelation rows

    pure (k relations)

  -- === 操作系 ===

  AddRelation toInit k -> do
    let init = toInit unit
    now <- recognize currentTimestamp
    newId <- recognize generateId

    let _ = execWithParams env.sql
          """
          INSERT INTO relation (id, kind, from_subject, to_thing, metadata,
                                valid_from, valid_until, contract_ref, created_at)
          VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
          """
          [ unsafeToForeign newId
          , unsafeToForeign (relationKindToString init.kind)
          , unsafeToForeign (unwrapSubjectId init.from)
          , unsafeToForeign (unwrapThingId init.to)
          , unsafeToForeign (metadataToJson init.metadata)
          , unsafeToForeign (unwrap now)
          , unsafeToForeign (maybeTimestampToForeign init.validUntil)
          , unsafeToForeign (maybeContractToForeign init.contractRef)
          , unsafeToForeign (unwrap now)
          ]

    -- Sediment を記録
    let _ = recordRelationSediment env newId "add" (metadataToJson init.metadata) now

    pure (k (mkRelationId newId))

  RemoveRelation rid _toUnit k -> do
    let ridStr = unwrapRelationId rid
    now <- recognize currentTimestamp

    -- 論理削除（removed_at を設定）
    let _ = execWithParams env.sql
          "UPDATE relation SET removed_at = ? WHERE id = ?"
          [ unsafeToForeign (unwrap now)
          , unsafeToForeign ridStr
          ]

    -- Sediment を記録
    sedimentId <- recordRelationSediment env ridStr "remove" "" now

    pure (k sedimentId)

  UpdateRelationMetadata rid toMeta k -> do
    let ridStr = unwrapRelationId rid
    let metadata = toMeta unit
    now <- recognize currentTimestamp

    let _ = execWithParams env.sql
          "UPDATE relation SET metadata = ? WHERE id = ?"
          [ unsafeToForeign (metadataToJsonString metadata)
          , unsafeToForeign ridStr
          ]

    -- Sediment を記録
    sedimentId <- recordRelationSediment env ridStr "update_metadata" (metadataToJsonString metadata) now

    pure (k sedimentId)

  -- === 所有権移転 ===

  RecordOwnershipTransfer toTransfer k -> do
    let transfer = toTransfer unit
    now <- recognize currentTimestamp
    logId <- recognize generateId

    -- 所有権移転ログを記録
    let _ = execWithParams env.sql
          """
          INSERT INTO ownership_transfer_log
            (id, thing_id, from_subject, to_subject, via_subject, contract_ref, created_at)
          VALUES (?, ?, ?, ?, ?, ?, ?)
          """
          [ unsafeToForeign logId
          , unsafeToForeign (unwrapThingId transfer.thing)
          , unsafeToForeign (unwrapSubjectId transfer.from)
          , unsafeToForeign (unwrapSubjectId transfer.to)
          , unsafeToForeign (maybeSubjectToForeign transfer.via)
          , unsafeToForeign (show transfer.contractRef)
          , unsafeToForeign (unwrap now)
          ]

    -- 旧所有者の Owns 関係を終了
    let _ = execWithParams env.sql
          """
          UPDATE relation SET removed_at = ?
          WHERE from_subject = ? AND to_thing = ? AND kind = 'Owns' AND removed_at IS NULL
          """
          [ unsafeToForeign (unwrap now)
          , unsafeToForeign (unwrapSubjectId transfer.from)
          , unsafeToForeign (unwrapThingId transfer.thing)
          ]

    -- 新所有者に Owns 関係を追加
    newRelId <- recognize generateId
    let _ = execWithParams env.sql
          """
          INSERT INTO relation (id, kind, from_subject, to_thing, metadata,
                                valid_from, valid_until, contract_ref, created_at)
          VALUES (?, 'Owns', ?, ?, NULL, ?, NULL, ?, ?)
          """
          [ unsafeToForeign newRelId
          , unsafeToForeign (unwrapSubjectId transfer.to)
          , unsafeToForeign (unwrapThingId transfer.thing)
          , unsafeToForeign (unwrap now)
          , unsafeToForeign (show transfer.contractRef)
          , unsafeToForeign (unwrap now)
          ]

    pure (k (mkSedimentId 1))

  -- === 集約照会 ===

  GetContents sid _toUnit k -> do
    let sidStr = unwrapSubjectId sid
    -- Contains または Guards 関係にある Thing を取得
    let cursor = execWithParams env.sql
          """
          SELECT DISTINCT to_thing
          FROM relation
          WHERE from_subject = ? AND kind IN ('Contains', 'Guards') AND removed_at IS NULL
          """
          [ unsafeToForeign sidStr ]

    let rows = toArray cursor
    let thingIds = map (\row -> mkThingId (unsafeFromForeign (getField row "to_thing"))) rows

    pure (k thingIds)

  GetObservedThings sid ctx _toUnit k -> do
    let sidStr = unwrapSubjectId sid
    -- Observes 関係にある Thing の View を取得
    let cursor = execWithParams env.sql
          """
          SELECT r.to_thing, r.metadata
          FROM relation r
          WHERE r.from_subject = ? AND r.kind = 'Observes' AND r.removed_at IS NULL
          """
          [ unsafeToForeign sidStr ]

    let rows = toArray cursor
    let views = map rowToThingView rows

    pure (k views)

  GetIntendedThings sid _toUnit k -> do
    let sidStr = unwrapSubjectId sid
    -- Intends 関係にある Thing の意図を取得
    let cursor = execWithParams env.sql
          """
          SELECT to_thing, metadata, valid_from, valid_until
          FROM relation
          WHERE from_subject = ? AND kind = 'Intends' AND removed_at IS NULL
          ORDER BY valid_from DESC
          """
          [ unsafeToForeign sidStr ]

    let rows = toArray cursor
    let intentions = map rowToIntentionView rows

    pure (k intentions)

-- ============================================================
-- Intent の実現（Realization）
-- ============================================================

-- | RelationIntent を実現する
-- |
-- | ## 哲学的基盤
-- |
-- | Husserl の「充実化」(Erfüllung):
-- | - 空虚な意志（Intent）が充実した事実（Factum）へと移行する過程
-- | - 「実行とは忘却である」：構造は消え、事実のみが残る
-- |
-- | 使用例:
-- | ```purescript
-- | result <- realizeRelationIntent env (getRelationsFrom sid kind) unit
-- | -- result :: Factum (Array Relation)
-- |
-- | -- エントリーポイントで Factum → Effect に変換
-- | handleFetch req = collapse do
-- |   result <- realizeRelationIntent env intent unit
-- |   ...
-- | ```
realizeRelationIntent :: forall a b. RelationEnv -> RelationIntent a b -> a -> Factum b
realizeRelationIntent env intent input =
  realizeInterpretation (interpretRelationF env) intent input

-- ============================================================
-- ヘルパー関数
-- ============================================================

-- | RelationKind を文字列に変換
relationKindToString :: RelationKind -> String
relationKindToString = case _ of
  Contains -> "Contains"
  Guards -> "Guards"
  Owns -> "Owns"
  Possesses -> "Possesses"
  Claims -> "Claims"
  Secures -> "Secures"
  SharedBy -> "SharedBy"
  Reserves -> "Reserves"
  Commits -> "Commits"
  Intends -> "Intends"
  Transports -> "Transports"
  Consigns -> "Consigns"
  ComposedOf -> "ComposedOf"
  BundledWith -> "BundledWith"
  Substitutes -> "Substitutes"
  Observes -> "Observes"
  Tracks -> "Tracks"
  ActsFor -> "ActsFor"
  Restricts -> "Restricts"

-- | 文字列を RelationKind に変換
stringToRelationKind :: String -> RelationKind
stringToRelationKind = case _ of
  "Contains" -> Contains
  "Guards" -> Guards
  "Owns" -> Owns
  "Possesses" -> Possesses
  "Claims" -> Claims
  "Secures" -> Secures
  "SharedBy" -> SharedBy
  "Reserves" -> Reserves
  "Commits" -> Commits
  "Intends" -> Intends
  "Transports" -> Transports
  "Consigns" -> Consigns
  "ComposedOf" -> ComposedOf
  "BundledWith" -> BundledWith
  "Substitutes" -> Substitutes
  "Observes" -> Observes
  "Tracks" -> Tracks
  "ActsFor" -> ActsFor
  "Restricts" -> Restricts
  _ -> Contains  -- デフォルト

-- | RelationMetadata を JSON 文字列に変換
metadataToJsonString :: RelationMetadata -> String
metadataToJsonString = case _ of
  SharedByMeta r -> """{"type":"SharedBy","share":""" <> show r.share <> "}"
  ActsForMeta r ->
    """{"type":"ActsFor","scope":"""
    <> "\"" <> agencyScopeToString r.scope <> "\""
    <> ""","disclosed":""" <> show r.disclosed <> "}"
  SecuresMeta r ->
    """{"type":"Secures","securityType":"""
    <> "\"" <> securityTypeToString r.securityType <> "\""
    <> ""","priority":""" <> show r.priority
    <> ""","amount":""" <> maybeShow r.amount
    <> "}"
  ExpirationMeta r ->
    """{"type":"Expiration","expiresAt":""" <> show (unwrap r.expiresAt) <> "}"
  ConditionalMeta r ->
    """{"type":"Conditional","pendingRelation":"""
    <> "\"" <> relationKindToString r.pendingRelation <> "\"}"
  IntendsMeta r ->
    """{"type":"Intends","quantity":""" <> show r.quantity
    <> ""","notifyOn":[""" <> Array.intercalate "," (map (show <<< changeTypeToString) r.notifyOn) <> "]}"

-- | Maybe RelationMetadata を Foreign に変換
metadataToJson :: Maybe RelationMetadata -> String
metadataToJson = case _ of
  Nothing -> ""
  Just meta -> metadataToJsonString meta

-- | SecurityType を文字列に変換
securityTypeToString :: SecurityType -> String
securityTypeToString = case _ of
  Pledge -> "Pledge"
  Lien -> "Lien"
  Mortgage -> "Mortgage"
  SecurityInterest -> "SecurityInterest"
  RetentionOfTitle -> "RetentionOfTitle"

-- | AgencyScope を文字列に変換
agencyScopeToString :: AgencyScope -> String
agencyScopeToString = case _ of
  GeneralAgency -> "GeneralAgency"
  SpecificAgency -> "SpecificAgency"
  LimitedAgency -> "LimitedAgency"

-- | ChangeType を文字列に変換
changeTypeToString :: ChangeType -> String
changeTypeToString = case _ of
  PriceChanged -> "PriceChanged"
  AvailabilityChanged -> "AvailabilityChanged"
  PropertyChanged -> "PropertyChanged"
  Discontinued -> "Discontinued"

-- | Maybe を表示
maybeShow :: forall a. Show a => Maybe a -> String
maybeShow = case _ of
  Nothing -> "null"
  Just a -> show a

-- | Maybe Timestamp を Foreign に変換
maybeTimestampToForeign :: Maybe Timestamp -> Foreign
maybeTimestampToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)
  Just (Timestamp ts) -> unsafeToForeign ts

-- | Maybe ContractId を Foreign に変換
maybeContractToForeign :: Maybe ContractId -> Foreign
maybeContractToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)
  Just cid -> unsafeToForeign (show cid)

-- | Maybe SubjectId を Foreign に変換
maybeSubjectToForeign :: Maybe SubjectId -> Foreign
maybeSubjectToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)
  Just sid -> unsafeToForeign (unwrapSubjectId sid)

-- | Relation Sediment を記録
recordRelationSediment :: RelationEnv -> String -> String -> String -> Timestamp -> Factum SedimentId
recordRelationSediment env relationId operation payload ts = do
  sedimentId <- recognize generateId

  -- 次のシーケンス番号を取得
  let seqCursor = execWithParams env.sql
        "SELECT COALESCE(MAX(sequence_id), 0) + 1 as next_seq FROM relation_sediment WHERE relation_id = ?"
        [ unsafeToForeign relationId ]
  let seqRow = one seqCursor
  let nextSeq = case seqRow of
        Nothing -> 1
        Just row -> unsafeFromForeign (getField row "next_seq") :: Int

  let _ = execWithParams env.sql
        """
        INSERT INTO relation_sediment (id, relation_id, sequence_id, operation, payload, created_at)
        VALUES (?, ?, ?, ?, ?, ?)
        """
        [ unsafeToForeign sedimentId
        , unsafeToForeign relationId
        , unsafeToForeign nextSeq
        , unsafeToForeign operation
        , unsafeToForeign payload
        , unsafeToForeign (unwrap ts)
        ]

  pure (mkSedimentId nextSeq)

-- | DB 行を Relation に変換
rowToRelation :: Foreign -> Relation
rowToRelation row =
  { id: mkRelationId (unsafeFromForeign (getField row "id"))
  , kind: stringToRelationKind (unsafeFromForeign (getField row "kind"))
  , from: mkSubjectId (unsafeFromForeign (getField row "from_subject"))
  , to: mkThingId (unsafeFromForeign (getField row "to_thing"))
  , metadata: Nothing  -- TODO: JSON パース
  , validFrom: Timestamp (unsafeFromForeign (getField row "valid_from"))
  , validUntil: Nothing  -- TODO: NULL 判定
  , contractRef: Nothing  -- TODO: NULL 判定
  , createdAt: Timestamp (unsafeFromForeign (getField row "created_at"))
  }

-- | DB 行を ThingView に変換
rowToThingView :: Foreign -> ThingView
rowToThingView row =
  { thingId: mkThingId (unsafeFromForeign (getField row "to_thing"))
  , visibleProperties: jsonNull  -- TODO: thing_property から取得
  , quantity: Nothing
  }

-- | DB 行を IntentionView に変換
rowToIntentionView :: Foreign -> IntentionView
rowToIntentionView row =
  { thingId: mkThingId (unsafeFromForeign (getField row "to_thing"))
  , quantity: mkQuantity 1  -- TODO: metadata から取得
  , intendedAt: Timestamp (unsafeFromForeign (getField row "valid_from"))
  , expiresAt: Nothing  -- TODO: valid_until から取得
  }
