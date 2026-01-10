-- | Noema Cognition: ThingInterpretation
-- |
-- | ThingF（物操作語彙）を Factum（事実）へ解釈する。
-- |
-- | ## 役割
-- |
-- | - GetProperty, SetProperty 等の物操作を SQLite 操作に変換
-- | - 時間構造（Retention, Primal, Protention）を実装
-- | - Subject に包摂される Thing の状態管理
-- |
-- | ## 圏論的解釈
-- |
-- | Interpretation は A-algebra homomorphism として機能:
-- | - ThingF は物操作の Functor
-- | - Interpretation は Intent（意志構造）を忘却し、
-- |   SQLite の状態変更という事実へ崩落させる
-- |
-- | > 実行とは忘却である。
-- |
-- | ## Thing の存在論的位置づけ
-- |
-- | Thing は意志を持たない物。Subject に「包摂」される。
-- | - Thing.situs: 包摂する Subject の ID
-- | - Thing の同一性 = ThingId（内部識別子）
-- | - SKU/JAN 等は PropertyKey として格納
-- |
-- | ## 時間構造（Husserl の内的時間意識）
-- |
-- | - Retention（把持）: 過去の Snapshot
-- | - Primal（原印象）: 現在の状態
-- | - Protention（予持）: 未来の Pending Intent
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | env <- recognize $ mkThingEnv sql
-- | result <- runThingIntent env (getProperty thingId key) unit
-- | -- result :: Factum PropertyValue
-- | ```
module Noema.Cognition.ThingInterpretation
  ( realizeThingIntent
  , ThingEnv
  , mkThingEnv
  , initializeThingSchema
  , interpretThingF
    -- * Abschattung インデックス
  , updateAbschattungIndex
  , queryByFacet
  , initializeAbschattungSchema
  ) where

import Prelude

import Data.Array (foldl)
import Data.Argonaut.Core (Json, stringify, jsonNull)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign, unsafeFromForeign)

import Noema.Topos.Situs
  ( ThingId
  , SubjectId
  , SedimentId(..)
  , Timestamp(..)
  , mkThingId
  , mkSubjectId
  , mkSedimentId
  , unwrapThingId
  , unwrapSubjectId
  , currentTimestamp
  )
import Noema.Vorzeichnung.Vocabulary.ThingF
  ( ThingF(..)
  , PropertyKey(..)
  , PropertyValue
  , ThingState
  , ThingSnapshot
  , Sediment
  , SitusChange
  , PendingIntent
  , ProtentionId(..)
  , ChangeReason(..)
  )
import Noema.Vorzeichnung.Intent (Intent, liftEffect)
import Noema.Cognition.Interpretation (Interpretation, realizeInterpretation)
import Noema.Sedimentation.Factum (Factum, recognize)
import Noema.Sedimentation.Abschattung
  ( Facet(..)
  , FacetKey
  , FacetValue
  , mkFacetKey
  , mkFacetValue
  , facetToString
  , parseFacet
  )
import Platform.Cloudflare.FFI.SqlStorage (SqlStorage)

-- Import from InventoryInterpretation (shared FFI)
import Noema.Cognition.InventoryInterpretation (Cursor, exec, execWithParams, one, toArray, getField, generateId)

-- ============================================================
-- 環境
-- ============================================================

-- | Thing Interpretation 環境
-- |
-- | SQLite Storage への参照を保持する。
type ThingEnv =
  { sql :: SqlStorage
  }

-- | 環境を作成
mkThingEnv :: SqlStorage -> ThingEnv
mkThingEnv sql = { sql }

-- ============================================================
-- スキーマ初期化
-- ============================================================

-- | Thing スキーマを初期化
-- |
-- | SubjectAttractor の初回アクセス時に呼び出す。
-- | Thing は Subject に包摂されるため、SubjectAttractor 内で管理。
initializeThingSchema :: SqlStorage -> Effect Unit
initializeThingSchema sql = do
  -- Thing テーブル（現在の状態）
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS thing (
      id TEXT PRIMARY KEY,
      situs TEXT NOT NULL,
      last_modified REAL NOT NULL,
      created_at REAL NOT NULL,
      FOREIGN KEY (situs) REFERENCES subject(id)
    )
  """

  -- Thing 属性テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS thing_property (
      thing_id TEXT NOT NULL,
      property_key TEXT NOT NULL,
      property_value TEXT NOT NULL,
      updated_at REAL NOT NULL,
      PRIMARY KEY (thing_id, property_key),
      FOREIGN KEY (thing_id) REFERENCES thing(id)
    )
  """

  -- Thing Sediment ログ（INSERT のみ、UPDATE 禁止）
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS thing_sediment (
      id TEXT PRIMARY KEY,
      thing_id TEXT NOT NULL,
      sequence_id INTEGER NOT NULL,
      intent_type TEXT NOT NULL,
      payload TEXT NOT NULL,
      created_at REAL NOT NULL,
      FOREIGN KEY (thing_id) REFERENCES thing(id)
    )
  """

  -- Situs 変更ログ
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS thing_situs_log (
      id TEXT PRIMARY KEY,
      thing_id TEXT NOT NULL,
      from_situs TEXT NOT NULL,
      to_situs TEXT NOT NULL,
      reason_type TEXT NOT NULL,
      reason_detail TEXT,
      contract_ref TEXT,
      created_at REAL NOT NULL,
      FOREIGN KEY (thing_id) REFERENCES thing(id)
    )
  """

  -- Protention（予持）テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS thing_protention (
      id TEXT PRIMARY KEY,
      thing_id TEXT NOT NULL,
      scheduled_at REAL NOT NULL,
      intent_body TEXT NOT NULL,
      condition TEXT,
      status TEXT NOT NULL DEFAULT 'pending',
      created_at REAL NOT NULL,
      FOREIGN KEY (thing_id) REFERENCES thing(id)
    )
  """

  -- インデックス
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_thing_situs ON thing(situs)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_thing_property ON thing_property(thing_id)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_thing_sediment_thing ON thing_sediment(thing_id, created_at)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_thing_situs_log ON thing_situs_log(thing_id, created_at)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_thing_protention ON thing_protention(thing_id, status)"

  pure unit

-- ============================================================
-- Intent の型定義
-- ============================================================

-- | ThingIntent の型エイリアス
type ThingIntent a b = Intent (ThingF Unit) a b

-- ============================================================
-- Interpretation 実装
-- ============================================================

-- | ThingF を Factum に解釈する Interpretation
-- |
-- | 圏論的解釈:
-- | この関数は自然変換 ThingF ~> Factum を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な SQLite 実装へ変換する。
interpretThingF :: ThingEnv -> Interpretation (ThingF Unit)
interpretThingF env = case _ of
  -- === 属性 (Property) ===

  GetProperty tid key _toUnit k -> do
    let tidStr = unwrapThingId tid
    let PropertyKey keyStr = key
    let cursor = execWithParams env.sql
          """
          SELECT property_value FROM thing_property
          WHERE thing_id = ? AND property_key = ?
          """
          [ unsafeToForeign tidStr
          , unsafeToForeign keyStr
          ]

    let maybeRow = one cursor
    let value = case maybeRow of
          Nothing -> jsonNull
          Just row ->
            let valueStr = unsafeFromForeign (getField row "property_value") :: String
            in case jsonParser valueStr of
                Left _ -> jsonNull
                Right json -> json

    pure (k value)

  SetProperty tid key toVal k -> do
    let tidStr = unwrapThingId tid
    let PropertyKey keyStr = key
    let value = toVal unit
    let valueStr = stringify value
    now <- recognize currentTimestamp

    -- Upsert property
    let _ = execWithParams env.sql
          """
          INSERT INTO thing_property (thing_id, property_key, property_value, updated_at)
          VALUES (?, ?, ?, ?)
          ON CONFLICT(thing_id, property_key) DO UPDATE SET
            property_value = excluded.property_value,
            updated_at = excluded.updated_at
          """
          [ unsafeToForeign tidStr
          , unsafeToForeign keyStr
          , unsafeToForeign valueStr
          , unsafeToForeign (unwrap now)
          ]

    -- Update thing's last_modified
    let _ = execWithParams env.sql
          "UPDATE thing SET last_modified = ? WHERE id = ?"
          [ unsafeToForeign (unwrap now)
          , unsafeToForeign tidStr
          ]

    -- Sediment ログを記録
    sedimentId <- recordSediment env tidStr "set_property" valueStr now

    pure (k sedimentId)

  -- === 位置 (Situs) ===

  GetSitus tid _toUnit k -> do
    let tidStr = unwrapThingId tid
    let cursor = execWithParams env.sql
          "SELECT situs FROM thing WHERE id = ?"
          [ unsafeToForeign tidStr ]

    let maybeRow = one cursor
    let situsId = case maybeRow of
          Nothing -> mkSubjectId "unknown"
          Just row -> mkSubjectId (unsafeFromForeign (getField row "situs"))

    pure (k situsId)

  RecordSitusChange tid toChange k -> do
    let tidStr = unwrapThingId tid
    let change = toChange unit
    now <- recognize currentTimestamp
    logId <- recognize generateId

    -- Situs 変更を記録
    let _ = execWithParams env.sql
          """
          INSERT INTO thing_situs_log (id, thing_id, from_situs, to_situs, reason_type, reason_detail, contract_ref, created_at)
          VALUES (?, ?, ?, ?, ?, ?, ?, ?)
          """
          [ unsafeToForeign logId
          , unsafeToForeign tidStr
          , unsafeToForeign (unwrapSubjectId change.from)
          , unsafeToForeign (unwrapSubjectId change.to)
          , unsafeToForeign (changeReasonType change.reason)
          , unsafeToForeign (changeReasonDetail change.reason)
          , unsafeToForeign (maybeToForeign (map show change.contractRef))
          , unsafeToForeign (unwrap now)
          ]

    -- Thing の situs を更新
    let _ = execWithParams env.sql
          "UPDATE thing SET situs = ?, last_modified = ? WHERE id = ?"
          [ unsafeToForeign (unwrapSubjectId change.to)
          , unsafeToForeign (unwrap now)
          , unsafeToForeign tidStr
          ]

    -- Sediment を記録
    sedimentId <- recordSediment env tidStr "situs_change" (stringify jsonNull) now

    pure (k sedimentId)

  -- === 時間 (Temporality) - Retention ===

  GetRetention tid ts _toUnit k -> do
    let tidStr = unwrapThingId tid
    let Timestamp tsVal = ts

    -- 指定時点での最新の Sediment を取得
    let cursor = execWithParams env.sql
          """
          SELECT * FROM thing_sediment
          WHERE thing_id = ? AND created_at <= ?
          ORDER BY created_at DESC
          LIMIT 1
          """
          [ unsafeToForeign tidStr
          , unsafeToForeign tsVal
          ]

    -- Snapshot を構築
    snapshot <- buildSnapshotAt env tidStr ts

    pure (k snapshot)

  GetRetentionRange tid range _toUnit k -> do
    let tidStr = unwrapThingId tid
    let Timestamp fromTs = range.from
    let Timestamp toTs = range.to

    let cursor = execWithParams env.sql
          """
          SELECT id, sequence_id, intent_type, payload, created_at
          FROM thing_sediment
          WHERE thing_id = ? AND created_at >= ? AND created_at <= ?
          ORDER BY created_at ASC
          """
          [ unsafeToForeign tidStr
          , unsafeToForeign fromTs
          , unsafeToForeign toTs
          ]

    let rows = toArray cursor
    let sediments = map rowToSediment rows

    pure (k sediments)

  -- === 時間 (Temporality) - Primal ===

  GetPrimal tid _toUnit k -> do
    let tidStr = unwrapThingId tid

    -- Thing の現在状態を取得
    state <- getCurrentState env tidStr

    pure (k state)

  -- === 時間 (Temporality) - Protention ===

  RegisterProtention tid toPending k -> do
    let tidStr = unwrapThingId tid
    let pending = toPending unit
    now <- recognize currentTimestamp
    protId <- recognize generateId

    let _ = execWithParams env.sql
          """
          INSERT INTO thing_protention (id, thing_id, scheduled_at, intent_body, condition, status, created_at)
          VALUES (?, ?, ?, ?, ?, 'pending', ?)
          """
          [ unsafeToForeign protId
          , unsafeToForeign tidStr
          , unsafeToForeign (unwrap pending.scheduledAt)
          , unsafeToForeign (stringify pending.intentBody)
          , unsafeToForeign (maybeToForeign pending.condition)
          , unsafeToForeign (unwrap now)
          ]

    pure (k (ProtentionId protId))

  GetProtentions tid _toUnit k -> do
    let tidStr = unwrapThingId tid
    let cursor = execWithParams env.sql
          """
          SELECT scheduled_at, intent_body, condition
          FROM thing_protention
          WHERE thing_id = ? AND status = 'pending'
          ORDER BY scheduled_at ASC
          """
          [ unsafeToForeign tidStr ]

    let rows = toArray cursor
    let pendings = map rowToPendingIntent rows

    pure (k pendings)

  RealizeProtention pid _toUnit k -> do
    let ProtentionId pidStr = pid
    now <- recognize currentTimestamp

    -- ステータスを realized に更新
    let _ = execWithParams env.sql
          "UPDATE thing_protention SET status = 'realized' WHERE id = ?"
          [ unsafeToForeign pidStr ]

    -- Sediment を記録
    -- TODO: thing_id を取得して記録
    pure (k (mkSedimentId 1))

  CancelProtention pid _toUnit k -> do
    let ProtentionId pidStr = pid

    let _ = execWithParams env.sql
          "UPDATE thing_protention SET status = 'cancelled' WHERE id = ?"
          [ unsafeToForeign pidStr ]

    pure (k unit)

-- ============================================================
-- Intent の実現（Realization）
-- ============================================================

-- | ThingIntent を実現する
-- |
-- | ## 哲学的基盤
-- |
-- | Husserl の「充実化」(Erfüllung):
-- | - 空虚な意志（Intent）が充実した事実（Factum）へと移行する過程
-- | - 「実行とは忘却である」：構造は消え、事実のみが残る
-- |
-- | 使用例:
-- | ```purescript
-- | result <- realizeThingIntent env (getProperty tid key) unit
-- | -- result :: Factum PropertyValue
-- |
-- | -- エントリーポイントで Factum → Effect に変換
-- | handleFetch req = collapse do
-- |   result <- realizeThingIntent env intent unit
-- |   ...
-- | ```
realizeThingIntent :: forall a b. ThingEnv -> ThingIntent a b -> a -> Factum b
realizeThingIntent env intent input =
  realizeInterpretation (interpretThingF env) intent input

-- ============================================================
-- ヘルパー関数
-- ============================================================

-- | Sediment を記録
recordSediment :: ThingEnv -> String -> String -> String -> Timestamp -> Factum SedimentId
recordSediment env thingId intentType payload ts = do
  sedimentId <- recognize generateId

  -- 次のシーケンス番号を取得
  let seqCursor = execWithParams env.sql
        "SELECT COALESCE(MAX(sequence_id), 0) + 1 as next_seq FROM thing_sediment WHERE thing_id = ?"
        [ unsafeToForeign thingId ]
  let seqRow = one seqCursor
  let nextSeq = case seqRow of
        Nothing -> 1
        Just row -> unsafeFromForeign (getField row "next_seq") :: Int

  let _ = execWithParams env.sql
        """
        INSERT INTO thing_sediment (id, thing_id, sequence_id, intent_type, payload, created_at)
        VALUES (?, ?, ?, ?, ?, ?)
        """
        [ unsafeToForeign sedimentId
        , unsafeToForeign thingId
        , unsafeToForeign nextSeq
        , unsafeToForeign intentType
        , unsafeToForeign payload
        , unsafeToForeign (unwrap ts)
        ]

  pure (mkSedimentId nextSeq)

-- | ChangeReason の型を取得
changeReasonType :: ChangeReason -> String
changeReasonType = case _ of
  Sale _ -> "sale"
  Purchase _ -> "purchase"
  Transfer -> "transfer"
  Return _ -> "return"
  Adjustment _ -> "adjustment"

-- | ChangeReason の詳細を取得
changeReasonDetail :: ChangeReason -> String
changeReasonDetail = case _ of
  Sale cid -> show cid
  Purchase cid -> show cid
  Transfer -> ""
  Return cid -> show cid
  Adjustment reason -> reason

-- | Maybe を Foreign に変換
maybeToForeign :: forall a. Maybe a -> Foreign
maybeToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)
  Just a -> unsafeToForeign a

-- | Thing の現在状態を取得
getCurrentState :: ThingEnv -> String -> Factum ThingState
getCurrentState env thingId = do
  -- Thing の基本情報を取得
  let thingCursor = execWithParams env.sql
        "SELECT id, situs, last_modified FROM thing WHERE id = ?"
        [ unsafeToForeign thingId ]

  let maybeRow = one thingCursor
  case maybeRow of
    Nothing ->
      -- Thing が存在しない場合はデフォルト状態
      pure
        { thingId: mkThingId thingId
        , properties: Map.empty
        , situs: mkSubjectId "unknown"
        , lastModified: Timestamp 0.0
        , protentions: []
        }
    Just row -> do
      let tid = mkThingId (unsafeFromForeign (getField row "id"))
      let situs = mkSubjectId (unsafeFromForeign (getField row "situs"))
      let lastMod = Timestamp (unsafeFromForeign (getField row "last_modified"))

      -- 属性を取得
      let propCursor = execWithParams env.sql
            "SELECT property_key, property_value FROM thing_property WHERE thing_id = ?"
            [ unsafeToForeign thingId ]
      let propRows = toArray propCursor
      let properties = foldl insertProperty Map.empty propRows

      -- Protention ID を取得
      let protCursor = execWithParams env.sql
            "SELECT id FROM thing_protention WHERE thing_id = ? AND status = 'pending'"
            [ unsafeToForeign thingId ]
      let protRows = toArray protCursor
      let protentions = map (\r -> ProtentionId (unsafeFromForeign (getField r "id"))) protRows

      pure
        { thingId: tid
        , properties
        , situs
        , lastModified: lastMod
        , protentions
        }
  where
    insertProperty :: Map PropertyKey PropertyValue -> Foreign -> Map PropertyKey PropertyValue
    insertProperty m row =
      let keyStr = unsafeFromForeign (getField row "property_key") :: String
          valueStr = unsafeFromForeign (getField row "property_value") :: String
          key = PropertyKey keyStr
          value = case jsonParser valueStr of
            Left _ -> jsonNull
            Right json -> json
      in Map.insert key value m

-- | 指定時点での Snapshot を構築
buildSnapshotAt :: ThingEnv -> String -> Timestamp -> Factum ThingSnapshot
buildSnapshotAt env thingId ts = do
  let Timestamp tsVal = ts

  -- 指定時点での Thing の状態を再構築
  -- Sediment を古い順に適用していく（イベントソーシング）
  let sedimentCursor = execWithParams env.sql
        """
        SELECT id, intent_type, payload, created_at
        FROM thing_sediment
        WHERE thing_id = ? AND created_at <= ?
        ORDER BY created_at DESC
        LIMIT 1
        """
        [ unsafeToForeign thingId
        , unsafeToForeign tsVal
        ]

  let maybeSediment = one sedimentCursor
  let sedimentId = case maybeSediment of
        Nothing -> mkSedimentId 0
        Just row -> mkSedimentId (unsafeFromForeign (getField row "id") :: Int)

  -- 属性を指定時点で取得
  let propCursor = execWithParams env.sql
        """
        SELECT property_key, property_value
        FROM thing_property
        WHERE thing_id = ? AND updated_at <= ?
        """
        [ unsafeToForeign thingId
        , unsafeToForeign tsVal
        ]
  let propRows = toArray propCursor
  let properties = foldl insertProp Map.empty propRows

  -- Situs を指定時点で取得
  let situsCursor = execWithParams env.sql
        """
        SELECT to_situs FROM thing_situs_log
        WHERE thing_id = ? AND created_at <= ?
        ORDER BY created_at DESC
        LIMIT 1
        """
        [ unsafeToForeign thingId
        , unsafeToForeign tsVal
        ]
  let situsRow = one situsCursor
  let situs = case situsRow of
        Nothing -> mkSubjectId "unknown"
        Just row -> mkSubjectId (unsafeFromForeign (getField row "to_situs"))

  pure
    { thingId: mkThingId thingId
    , timestamp: ts
    , properties
    , situs
    , sedimentId
    }
  where
    insertProp :: Map PropertyKey PropertyValue -> Foreign -> Map PropertyKey PropertyValue
    insertProp m row =
      let keyStr = unsafeFromForeign (getField row "property_key") :: String
          valueStr = unsafeFromForeign (getField row "property_value") :: String
          key = PropertyKey keyStr
          value = case jsonParser valueStr of
            Left _ -> jsonNull
            Right json -> json
      in Map.insert key value m

-- | Sediment 行を変換
rowToSediment :: Foreign -> Sediment
rowToSediment row =
  { sequenceId: unsafeFromForeign (getField row "sequence_id")
  , intentType: unsafeFromForeign (getField row "intent_type")
  , payload: case jsonParser (unsafeFromForeign (getField row "payload")) of
      Left _ -> jsonNull
      Right json -> json
  , createdAt: Timestamp (unsafeFromForeign (getField row "created_at"))
  }

-- | PendingIntent 行を変換
rowToPendingIntent :: Foreign -> PendingIntent
rowToPendingIntent row =
  { scheduledAt: Timestamp (unsafeFromForeign (getField row "scheduled_at"))
  , intentBody: case jsonParser (unsafeFromForeign (getField row "intent_body")) of
      Left _ -> jsonNull
      Right json -> json
  , condition: Nothing  -- TODO: NULL 判定
  }

-- ============================================================
-- Abschattung インデックス
-- ============================================================

-- | Abschattung スキーマを初期化
-- |
-- | Thing の多面的インデックス用テーブルを作成する。
initializeAbschattungSchema :: SqlStorage -> Effect Unit
initializeAbschattungSchema sql = do
  -- Abschattung インデックステーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS abschattung_index (
      id TEXT PRIMARY KEY,
      subject_id TEXT NOT NULL,
      facet_type TEXT NOT NULL,
      facet_param TEXT,
      index_key TEXT NOT NULL,
      thing_id TEXT NOT NULL,
      sediment_id INTEGER NOT NULL,
      created_at REAL NOT NULL
    )
  """

  -- インデックス（検索高速化）
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_abschattung_facet ON abschattung_index(facet_type, index_key)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_abschattung_thing ON abschattung_index(thing_id)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_abschattung_subject ON abschattung_index(subject_id)"

  pure unit

-- | Abschattung インデックスを更新
-- |
-- | Thing のプロパティ変更時に呼び出し、インデックスを更新する。
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | -- SKU でインデックス
-- | updateAbschattungIndex env subjectId thingId FacetBySKU "SKU-001" sedimentId
-- |
-- | -- プロパティでインデックス
-- | updateAbschattungIndex env subjectId thingId (FacetByProperty "color") "red" sedimentId
-- | ```
updateAbschattungIndex
  :: ThingEnv
  -> SubjectId
  -> ThingId
  -> Facet
  -> String        -- index key
  -> SedimentId
  -> Factum Unit
updateAbschattungIndex env subjectId thingId facet indexKey sedimentId = do
  now <- recognize currentTimestamp
  entryId <- recognize generateId

  let facetType = facetToString facet
  let facetParam = case facet of
        FacetByProperty key -> Just key
        FacetByRelation rel -> Just rel
        FacetByChannel ch -> Just ch
        _ -> Nothing

  -- 既存のエントリを削除（同一 Thing/Facet/Key の重複を防ぐ）
  let _ = execWithParams env.sql
        """
        DELETE FROM abschattung_index
        WHERE thing_id = ? AND facet_type = ? AND index_key = ?
        """
        [ unsafeToForeign (unwrapThingId thingId)
        , unsafeToForeign facetType
        , unsafeToForeign indexKey
        ]

  -- 新しいエントリを挿入
  let _ = execWithParams env.sql
        """
        INSERT INTO abschattung_index
          (id, subject_id, facet_type, facet_param, index_key, thing_id, sediment_id, created_at)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """
        [ unsafeToForeign entryId
        , unsafeToForeign (unwrapSubjectId subjectId)
        , unsafeToForeign facetType
        , unsafeToForeign (maybeToForeign facetParam)
        , unsafeToForeign indexKey
        , unsafeToForeign (unwrapThingId thingId)
        , unsafeToForeign (unwrap sedimentId)
        , unsafeToForeign (unwrap now)
        ]

  pure unit

-- | Facet とキーで Thing を検索
-- |
-- | Abschattung インデックスを使用して Thing ID のリストを取得する。
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | -- SKU で検索
-- | thingIds <- queryByFacet env FacetBySKU "SKU-001"
-- |
-- | -- 位置で検索
-- | thingIds <- queryByFacet env FacetBySitus "warehouse-001"
-- | ```
queryByFacet
  :: ThingEnv
  -> Facet
  -> String        -- index key
  -> Factum (Array ThingId)
queryByFacet env facet indexKey = do
  let facetType = facetToString facet

  let cursor = execWithParams env.sql
        """
        SELECT thing_id FROM abschattung_index
        WHERE facet_type = ? AND index_key = ?
        ORDER BY created_at DESC
        """
        [ unsafeToForeign facetType
        , unsafeToForeign indexKey
        ]

  let rows = toArray cursor
  let thingIds = map (\row -> mkThingId (unsafeFromForeign (getField row "thing_id"))) rows

  pure thingIds

