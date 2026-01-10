-- | Noema Cognition: ContractInterpretation
-- |
-- | ContractF（契約語彙）を Factum（事実）へ解釈する。
-- |
-- | ## 役割
-- |
-- | - ProposeContract, AcceptContract 等の契約ライフサイクルを SQLite 操作に変換
-- | - 義務（Obligation）の管理と履行追跡
-- | - 契約間関係（前提、従属、対価、担保、変更、解除）の管理
-- |
-- | ## 圏論的解釈
-- |
-- | Interpretation は A-algebra homomorphism として機能:
-- | - ContractF は契約操作の Functor（規定の圏の操作）
-- | - Interpretation は Intent（意志構造）を忘却し、
-- |   SQLite の状態変更という事実へ崩落させる
-- |
-- | > 実行とは忘却である。
-- |
-- | ## 契約の存在論的位置づけ
-- |
-- | Contract は DO として実装される。
-- | Nomos（大域意志）に依拠し、Subject 間の権利義務関係を規定する。
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | env <- recognize $ mkContractEnv sql
-- | result <- realizeContractIntent env (getContract cid) unit
-- | -- result :: Factum ContractState
-- | ```
module Noema.Cognition.ContractInterpretation
  ( realizeContractIntent
  , ContractEnv
  , mkContractEnv
  , initializeContractSchema
  , interpretContractF
  ) where

import Prelude

import Data.Array as Array
import Data.Traversable (traverse)
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
  , ContractId
  , SedimentId
  , Timestamp(..)
  , currentTimestamp
  , mkSubjectId
  , mkThingId
  , mkContractId
  , mkSedimentId
  , unwrapSubjectId
  , unwrapThingId
  , unwrapContractId
  )
import Noema.Topos.Nomos (NomosReference)
import Noema.Vorzeichnung.Vocabulary.ContractF
  ( ContractF(..)
  , ContractStatus(..)
  , ObligationKind(..)
  , ObligationStatus(..)
  , Obligation
  , ContractParties
  , ContractState
  , ContractRelationKind(..)
  , ContractRelation
  , ContractGraph
  )
import Noema.Vorzeichnung.Intent (Intent)
import Noema.Cognition.Interpretation (Interpretation, realizeInterpretation)
import Noema.Sedimentation.Factum (Factum, recognize)
import Platform.Cloudflare.FFI.SqlStorage (SqlStorage)

-- Import from InventoryInterpretation (shared FFI)
import Noema.Cognition.InventoryInterpretation (exec, execWithParams, one, toArray, getField, generateId)

-- ============================================================
-- 環境
-- ============================================================

-- | Contract Interpretation 環境
-- |
-- | SQLite Storage への参照を保持する。
type ContractEnv =
  { sql :: SqlStorage
  }

-- | 環境を作成
mkContractEnv :: SqlStorage -> ContractEnv
mkContractEnv sql = { sql }

-- ============================================================
-- スキーマ初期化
-- ============================================================

-- | Contract スキーマを初期化
-- |
-- | ContractAttractor（将来の DO）または SubjectAttractor から呼び出す。
initializeContractSchema :: SqlStorage -> Effect Unit
initializeContractSchema sql = do
  -- Contract テーブル（契約マスタ）
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS contract (
      id TEXT PRIMARY KEY,
      party_a TEXT NOT NULL,
      party_b TEXT NOT NULL,
      status TEXT NOT NULL DEFAULT 'Draft',
      nomos_ref TEXT,
      created_at REAL NOT NULL,
      updated_at REAL NOT NULL
    )
  """

  -- Contract 条項テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS contract_term (
      id TEXT PRIMARY KEY,
      contract_id TEXT NOT NULL,
      term_order INTEGER NOT NULL,
      term_content TEXT NOT NULL,
      FOREIGN KEY (contract_id) REFERENCES contract(id)
    )
  """

  -- Contract 対象 Thing テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS contract_thing_ref (
      contract_id TEXT NOT NULL,
      thing_id TEXT NOT NULL,
      PRIMARY KEY (contract_id, thing_id),
      FOREIGN KEY (contract_id) REFERENCES contract(id)
    )
  """

  -- 義務テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS obligation (
      id TEXT PRIMARY KEY,
      contract_id TEXT NOT NULL,
      kind TEXT NOT NULL,
      debtor TEXT NOT NULL,
      creditor TEXT NOT NULL,
      thing_ref TEXT,
      amount REAL,
      due_date REAL,
      status TEXT NOT NULL DEFAULT 'Pending',
      created_at REAL NOT NULL,
      FOREIGN KEY (contract_id) REFERENCES contract(id)
    )
  """

  -- 履行証明テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS fulfillment_proof (
      id TEXT PRIMARY KEY,
      obligation_id TEXT NOT NULL,
      evidence TEXT NOT NULL,
      created_at REAL NOT NULL,
      FOREIGN KEY (obligation_id) REFERENCES obligation(id)
    )
  """

  -- 契約間関係テーブル
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS contract_relation (
      id TEXT PRIMARY KEY,
      from_contract TEXT NOT NULL,
      to_contract TEXT NOT NULL,
      kind TEXT NOT NULL,
      description TEXT,
      created_at REAL NOT NULL,
      FOREIGN KEY (from_contract) REFERENCES contract(id),
      FOREIGN KEY (to_contract) REFERENCES contract(id)
    )
  """

  -- 契約 Sediment ログ（INSERT のみ）
  let _ = exec sql """
    CREATE TABLE IF NOT EXISTS contract_sediment (
      id TEXT PRIMARY KEY,
      contract_id TEXT NOT NULL,
      sequence_id INTEGER NOT NULL,
      operation TEXT NOT NULL,
      payload TEXT NOT NULL,
      created_at REAL NOT NULL,
      FOREIGN KEY (contract_id) REFERENCES contract(id)
    )
  """

  -- インデックス
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_contract_parties ON contract(party_a, party_b)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_contract_status ON contract(status)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_obligation_contract ON obligation(contract_id)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_obligation_debtor ON obligation(debtor, status)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_contract_relation_from ON contract_relation(from_contract)"
  let _ = exec sql "CREATE INDEX IF NOT EXISTS idx_contract_relation_to ON contract_relation(to_contract)"

  pure unit

-- ============================================================
-- Intent の型定義
-- ============================================================

-- | ContractIntent の型エイリアス
type ContractIntent a b = Intent (ContractF Unit) a b

-- ============================================================
-- Interpretation 実装
-- ============================================================

-- | ContractF を Factum に解釈する Interpretation
-- |
-- | 圏論的解釈:
-- | この関数は自然変換 ContractF ~> Factum を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な SQLite 実装へ変換する。
interpretContractF :: ContractEnv -> Interpretation (ContractF Unit)
interpretContractF env = case _ of
  -- === ライフサイクル ===

  ProposeContract toProposal k -> do
    let proposal = toProposal unit
    now <- recognize currentTimestamp
    newId <- recognize generateId

    -- Contract を INSERT
    let _ = execWithParams env.sql
          """
          INSERT INTO contract (id, party_a, party_b, status, nomos_ref, created_at, updated_at)
          VALUES (?, ?, ?, 'Proposed', ?, ?, ?)
          """
          [ unsafeToForeign newId
          , unsafeToForeign (unwrapSubjectId proposal.parties.partyA)
          , unsafeToForeign (unwrapSubjectId proposal.parties.partyB)
          , unsafeToForeign (nomosRefToString proposal.nomosRef)
          , unsafeToForeign (unwrap now)
          , unsafeToForeign (unwrap now)
          ]

    -- 条項を INSERT
    _ <- insertTerms env newId proposal.terms

    -- Thing 参照を INSERT
    _ <- insertThingRefs env newId proposal.thingRefs

    -- Sediment を記録
    let _ = recordContractSediment env newId "propose" "" now

    pure (k (mkContractId newId))

  AcceptContract cid _toUnit k -> do
    let cidStr = unwrapContractId cid
    now <- recognize currentTimestamp

    -- ステータスを Accepted に更新
    let _ = execWithParams env.sql
          "UPDATE contract SET status = 'Accepted', updated_at = ? WHERE id = ?"
          [ unsafeToForeign (unwrap now)
          , unsafeToForeign cidStr
          ]

    -- Sediment を記録
    sedimentId <- recordContractSediment env cidStr "accept" "" now

    pure (k sedimentId)

  RejectContract cid toReason k -> do
    let cidStr = unwrapContractId cid
    let reason = toReason unit
    now <- recognize currentTimestamp

    -- ステータスを Cancelled に更新（拒否は取消扱い）
    let _ = execWithParams env.sql
          "UPDATE contract SET status = 'Cancelled', updated_at = ? WHERE id = ?"
          [ unsafeToForeign (unwrap now)
          , unsafeToForeign cidStr
          ]

    -- Sediment を記録
    sedimentId <- recordContractSediment env cidStr "reject" reason now

    pure (k sedimentId)

  CancelContract cid toReason k -> do
    let cidStr = unwrapContractId cid
    let reason = toReason unit
    now <- recognize currentTimestamp

    -- ステータスを Cancelled に更新
    let _ = execWithParams env.sql
          "UPDATE contract SET status = 'Cancelled', updated_at = ? WHERE id = ?"
          [ unsafeToForeign (unwrap now)
          , unsafeToForeign cidStr
          ]

    -- Sediment を記録
    sedimentId <- recordContractSediment env cidStr "cancel" reason now

    pure (k sedimentId)

  -- === 照会 ===

  GetContract cid _toUnit k -> do
    let cidStr = unwrapContractId cid
    state <- getContractState env cidStr

    pure (k state)

  GetContractsByParty sid _toUnit k -> do
    let sidStr = unwrapSubjectId sid
    let cursor = execWithParams env.sql
          """
          SELECT id FROM contract
          WHERE (party_a = ? OR party_b = ?)
          ORDER BY created_at DESC
          """
          [ unsafeToForeign sidStr
          , unsafeToForeign sidStr
          ]

    let rows = toArray cursor
    states <- traverse (\row -> getContractState env (unsafeFromForeign (getField row "id"))) rows

    pure (k states)

  -- === 義務 ===

  AddObligation cid toDef k -> do
    let cidStr = unwrapContractId cid
    let def = toDef unit
    now <- recognize currentTimestamp
    oblId <- recognize generateId

    let _ = execWithParams env.sql
          """
          INSERT INTO obligation (id, contract_id, kind, debtor, creditor, thing_ref, amount, due_date, status, created_at)
          VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'Pending', ?)
          """
          [ unsafeToForeign oblId
          , unsafeToForeign cidStr
          , unsafeToForeign (obligationKindToString def.kind)
          , unsafeToForeign (unwrapSubjectId def.debtor)
          , unsafeToForeign (unwrapSubjectId def.creditor)
          , unsafeToForeign (maybeThingToForeign def.thingRef)
          , unsafeToForeign (maybeNumberToForeign def.amount)
          , unsafeToForeign (maybeTimestampToForeign def.dueDate)
          , unsafeToForeign (unwrap now)
          ]

    -- Contract の updated_at を更新
    let _ = execWithParams env.sql
          "UPDATE contract SET updated_at = ? WHERE id = ?"
          [ unsafeToForeign (unwrap now)
          , unsafeToForeign cidStr
          ]

    pure (k oblId)

  FulfillObligation oblId toProof k -> do
    let proof = toProof unit
    now <- recognize currentTimestamp
    proofId <- recognize generateId

    -- 履行証明を記録
    let _ = execWithParams env.sql
          """
          INSERT INTO fulfillment_proof (id, obligation_id, evidence, created_at)
          VALUES (?, ?, ?, ?)
          """
          [ unsafeToForeign proofId
          , unsafeToForeign oblId
          , unsafeToForeign (stringify proof.evidence)
          , unsafeToForeign (unwrap now)
          ]

    -- 義務のステータスを Fulfilled に更新
    let _ = execWithParams env.sql
          "UPDATE obligation SET status = 'Fulfilled' WHERE id = ?"
          [ unsafeToForeign oblId ]

    -- Contract の updated_at を更新（契約 ID を取得）
    let cidCursor = execWithParams env.sql
          "SELECT contract_id FROM obligation WHERE id = ?"
          [ unsafeToForeign oblId ]
    let cidRow = one cidCursor
    case cidRow of
      Just row -> do
        let cidStr = unsafeFromForeign (getField row "contract_id") :: String
        let _ = execWithParams env.sql
              "UPDATE contract SET updated_at = ? WHERE id = ?"
              [ unsafeToForeign (unwrap now)
              , unsafeToForeign cidStr
              ]
        -- すべての義務が履行されたか確認
        _ <- checkAndUpdateContractStatus env cidStr now
        pure unit
      Nothing -> pure unit

    pure (k (mkSedimentId 1))

  GetObligations cid _toUnit k -> do
    let cidStr = unwrapContractId cid
    let cursor = execWithParams env.sql
          """
          SELECT id, kind, debtor, creditor, thing_ref, amount, due_date, status
          FROM obligation
          WHERE contract_id = ?
          ORDER BY created_at ASC
          """
          [ unsafeToForeign cidStr ]

    let rows = toArray cursor
    let obligations = map rowToObligation rows

    pure (k obligations)

  GetPendingObligations sid _toUnit k -> do
    let sidStr = unwrapSubjectId sid
    let cursor = execWithParams env.sql
          """
          SELECT o.id, o.kind, o.debtor, o.creditor, o.thing_ref, o.amount, o.due_date, o.status
          FROM obligation o
          WHERE o.debtor = ? AND o.status = 'Pending'
          ORDER BY o.due_date ASC NULLS LAST
          """
          [ unsafeToForeign sidStr ]

    let rows = toArray cursor
    let obligations = map rowToObligation rows

    pure (k obligations)

  -- === 契約間関係 ===

  LinkContracts toRelation k -> do
    let rel = toRelation unit
    now <- recognize currentTimestamp
    relId <- recognize generateId

    let _ = execWithParams env.sql
          """
          INSERT INTO contract_relation (id, from_contract, to_contract, kind, description, created_at)
          VALUES (?, ?, ?, ?, ?, ?)
          """
          [ unsafeToForeign relId
          , unsafeToForeign (unwrapContractId rel.from)
          , unsafeToForeign (unwrapContractId rel.to)
          , unsafeToForeign (contractRelationKindToString rel.kind)
          , unsafeToForeign (maybeStringToForeign rel.description)
          , unsafeToForeign (unwrap now)
          ]

    pure (k (mkSedimentId 1))

  GetLinkedContracts cid kind _toUnit k -> do
    let cidStr = unwrapContractId cid
    let kindStr = contractRelationKindToString kind
    let cursor = execWithParams env.sql
          """
          SELECT to_contract FROM contract_relation
          WHERE from_contract = ? AND kind = ?
          """
          [ unsafeToForeign cidStr
          , unsafeToForeign kindStr
          ]

    let rows = toArray cursor
    let contractIds = map (\row -> mkContractId (unsafeFromForeign (getField row "to_contract"))) rows

    pure (k contractIds)

  GetContractChain cid _toUnit k -> do
    let cidStr = unwrapContractId cid
    graph <- buildContractGraph env cidStr

    pure (k graph)

-- ============================================================
-- Intent の実現（Realization）
-- ============================================================

-- | ContractIntent を実現する
-- |
-- | ## 哲学的基盤
-- |
-- | Husserl の「充実化」(Erfüllung):
-- | - 空虚な意志（Intent）が充実した事実（Factum）へと移行する過程
-- | - 「実行とは忘却である」：構造は消え、事実のみが残る
realizeContractIntent :: forall a b. ContractEnv -> ContractIntent a b -> a -> Factum b
realizeContractIntent env intent input =
  realizeInterpretation (interpretContractF env) intent input

-- ============================================================
-- ヘルパー関数
-- ============================================================

-- | NomosReference を文字列に変換
nomosRefToString :: NomosReference -> String
nomosRefToString ref = show ref.version

-- | 条項を INSERT
insertTerms :: ContractEnv -> String -> Array Json -> Factum Unit
insertTerms env contractId terms = do
  _ <- traverseWithIndex insertTerm terms
  pure unit
  where
    insertTerm idx term = do
      termId <- recognize generateId
      let _ = execWithParams env.sql
            """
            INSERT INTO contract_term (id, contract_id, term_order, term_content)
            VALUES (?, ?, ?, ?)
            """
            [ unsafeToForeign termId
            , unsafeToForeign contractId
            , unsafeToForeign idx
            , unsafeToForeign (stringify term)
            ]
      pure unit

-- | インデックス付き traverse
traverseWithIndex :: forall a b. (Int -> a -> Factum b) -> Array a -> Factum (Array b)
traverseWithIndex f arr = go 0 arr []
  where
    go _ [] acc = pure (Array.reverse acc)
    go idx rest acc = case Array.uncons rest of
      Nothing -> pure (Array.reverse acc)
      Just { head, tail } -> do
        result <- f idx head
        go (idx + 1) tail (Array.cons result acc)

-- | Thing 参照を INSERT
insertThingRefs :: ContractEnv -> String -> Array ThingId -> Factum Unit
insertThingRefs env contractId thingIds = do
  _ <- traverse insertRef thingIds
  pure unit
  where
    insertRef tid = do
      let _ = execWithParams env.sql
            """
            INSERT INTO contract_thing_ref (contract_id, thing_id)
            VALUES (?, ?)
            """
            [ unsafeToForeign contractId
            , unsafeToForeign (unwrapThingId tid)
            ]
      pure unit

-- | Contract Sediment を記録
recordContractSediment :: ContractEnv -> String -> String -> String -> Timestamp -> Factum SedimentId
recordContractSediment env contractId operation payload ts = do
  sedimentId <- recognize generateId

  -- 次のシーケンス番号を取得
  let seqCursor = execWithParams env.sql
        "SELECT COALESCE(MAX(sequence_id), 0) + 1 as next_seq FROM contract_sediment WHERE contract_id = ?"
        [ unsafeToForeign contractId ]
  let seqRow = one seqCursor
  let nextSeq = case seqRow of
        Nothing -> 1
        Just row -> unsafeFromForeign (getField row "next_seq") :: Int

  let _ = execWithParams env.sql
        """
        INSERT INTO contract_sediment (id, contract_id, sequence_id, operation, payload, created_at)
        VALUES (?, ?, ?, ?, ?, ?)
        """
        [ unsafeToForeign sedimentId
        , unsafeToForeign contractId
        , unsafeToForeign nextSeq
        , unsafeToForeign operation
        , unsafeToForeign payload
        , unsafeToForeign (unwrap ts)
        ]

  pure (mkSedimentId nextSeq)

-- | Contract 状態を取得
getContractState :: ContractEnv -> String -> Factum ContractState
getContractState env contractId = do
  let cursor = execWithParams env.sql
        """
        SELECT id, party_a, party_b, status, created_at, updated_at
        FROM contract
        WHERE id = ?
        """
        [ unsafeToForeign contractId ]

  let maybeRow = one cursor
  case maybeRow of
    Nothing ->
      -- デフォルト状態を返す
      pure
        { id: mkContractId contractId
        , parties: { partyA: mkSubjectId "unknown", partyB: mkSubjectId "unknown" }
        , terms: []
        , thingRefs: []
        , status: Draft
        , obligations: []
        , createdAt: Timestamp 0.0
        , updatedAt: Timestamp 0.0
        }
    Just row -> do
      -- 条項を取得
      terms <- getContractTerms env contractId

      -- Thing 参照を取得
      thingRefs <- getContractThingRefs env contractId

      -- 義務を取得
      let oblCursor = execWithParams env.sql
            "SELECT id, kind, debtor, creditor, thing_ref, amount, due_date, status FROM obligation WHERE contract_id = ?"
            [ unsafeToForeign contractId ]
      let oblRows = toArray oblCursor
      let obligations = map rowToObligation oblRows

      pure
        { id: mkContractId (unsafeFromForeign (getField row "id"))
        , parties:
            { partyA: mkSubjectId (unsafeFromForeign (getField row "party_a"))
            , partyB: mkSubjectId (unsafeFromForeign (getField row "party_b"))
            }
        , terms
        , thingRefs
        , status: stringToContractStatus (unsafeFromForeign (getField row "status"))
        , obligations
        , createdAt: Timestamp (unsafeFromForeign (getField row "created_at"))
        , updatedAt: Timestamp (unsafeFromForeign (getField row "updated_at"))
        }

-- | 条項を取得
getContractTerms :: ContractEnv -> String -> Factum (Array Json)
getContractTerms env contractId = do
  let cursor = execWithParams env.sql
        "SELECT term_content FROM contract_term WHERE contract_id = ? ORDER BY term_order"
        [ unsafeToForeign contractId ]
  let rows = toArray cursor
  pure $ map (\row ->
    let content = unsafeFromForeign (getField row "term_content") :: String
    in case jsonParser content of
         Left _ -> jsonNull
         Right json -> json
  ) rows

-- | Thing 参照を取得
getContractThingRefs :: ContractEnv -> String -> Factum (Array ThingId)
getContractThingRefs env contractId = do
  let cursor = execWithParams env.sql
        "SELECT thing_id FROM contract_thing_ref WHERE contract_id = ?"
        [ unsafeToForeign contractId ]
  let rows = toArray cursor
  pure $ map (\row -> mkThingId (unsafeFromForeign (getField row "thing_id"))) rows

-- | 義務をすべて履行したか確認し、Contract ステータスを更新
checkAndUpdateContractStatus :: ContractEnv -> String -> Timestamp -> Factum Unit
checkAndUpdateContractStatus env contractId now = do
  let cursor = execWithParams env.sql
        "SELECT COUNT(*) as pending_count FROM obligation WHERE contract_id = ? AND status = 'Pending'"
        [ unsafeToForeign contractId ]
  let maybeRow = one cursor
  case maybeRow of
    Just row -> do
      let pendingCount = unsafeFromForeign (getField row "pending_count") :: Int
      when (pendingCount == 0) do
        -- すべて履行済み → Fulfilled に更新
        let _ = execWithParams env.sql
              "UPDATE contract SET status = 'Fulfilled', updated_at = ? WHERE id = ?"
              [ unsafeToForeign (unwrap now)
              , unsafeToForeign contractId
              ]
        pure unit
    Nothing -> pure unit

-- | 契約グラフを構築
buildContractGraph :: ContractEnv -> String -> Factum ContractGraph
buildContractGraph env startContractId = do
  -- 起点の契約を取得
  startState <- getContractState env startContractId

  -- 関連する契約を取得（直接のリンクのみ、深い探索は将来の拡張）
  let relCursor = execWithParams env.sql
        """
        SELECT from_contract, to_contract, kind, description
        FROM contract_relation
        WHERE from_contract = ? OR to_contract = ?
        """
        [ unsafeToForeign startContractId
        , unsafeToForeign startContractId
        ]
  let relRows = toArray relCursor
  let relations = map rowToContractRelation relRows

  -- リンク先の契約を取得
  let linkedIds = Array.nub $ Array.filter (_ /= startContractId) $
        Array.concatMap (\r -> [unwrapContractId r.from, unwrapContractId r.to]) relations
  linkedStates <- traverse (getContractState env) linkedIds

  pure
    { contracts: Array.cons startState linkedStates
    , relations
    }

-- | ContractStatus を文字列に変換
contractStatusToString :: ContractStatus -> String
contractStatusToString = case _ of
  Draft -> "Draft"
  Proposed -> "Proposed"
  Accepted -> "Accepted"
  InProgress -> "InProgress"
  Fulfilled -> "Fulfilled"
  Cancelled -> "Cancelled"
  Disputed -> "Disputed"

-- | 文字列を ContractStatus に変換
stringToContractStatus :: String -> ContractStatus
stringToContractStatus = case _ of
  "Draft" -> Draft
  "Proposed" -> Proposed
  "Accepted" -> Accepted
  "InProgress" -> InProgress
  "Fulfilled" -> Fulfilled
  "Cancelled" -> Cancelled
  "Disputed" -> Disputed
  _ -> Draft

-- | ObligationKind を文字列に変換
obligationKindToString :: ObligationKind -> String
obligationKindToString = case _ of
  Transfer_ -> "Transfer"
  Payment -> "Payment"
  Perform -> "Perform"
  Refrain -> "Refrain"

-- | 文字列を ObligationKind に変換
stringToObligationKind :: String -> ObligationKind
stringToObligationKind = case _ of
  "Transfer" -> Transfer_
  "Payment" -> Payment
  "Perform" -> Perform
  "Refrain" -> Refrain
  _ -> Perform

-- | ObligationStatus を文字列に変換
obligationStatusToString :: ObligationStatus -> String
obligationStatusToString = case _ of
  Pending -> "Pending"
  Fulfilled_ -> "Fulfilled"
  Breached -> "Breached"
  Waived -> "Waived"

-- | 文字列を ObligationStatus に変換
stringToObligationStatus :: String -> ObligationStatus
stringToObligationStatus = case _ of
  "Pending" -> Pending
  "Fulfilled" -> Fulfilled_
  "Breached" -> Breached
  "Waived" -> Waived
  _ -> Pending

-- | ContractRelationKind を文字列に変換
contractRelationKindToString :: ContractRelationKind -> String
contractRelationKindToString = case _ of
  Prerequisite -> "Prerequisite"
  Subordinate -> "Subordinate"
  Consideration -> "Consideration"
  Security -> "Security"
  Amendment -> "Amendment"
  Termination -> "Termination"

-- | 文字列を ContractRelationKind に変換
stringToContractRelationKind :: String -> ContractRelationKind
stringToContractRelationKind = case _ of
  "Prerequisite" -> Prerequisite
  "Subordinate" -> Subordinate
  "Consideration" -> Consideration
  "Security" -> Security
  "Amendment" -> Amendment
  "Termination" -> Termination
  _ -> Prerequisite

-- | Maybe ThingId を Foreign に変換
maybeThingToForeign :: Maybe ThingId -> Foreign
maybeThingToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)
  Just tid -> unsafeToForeign (unwrapThingId tid)

-- | Maybe Number を Foreign に変換
maybeNumberToForeign :: Maybe Number -> Foreign
maybeNumberToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)
  Just n -> unsafeToForeign n

-- | Maybe Timestamp を Foreign に変換
maybeTimestampToForeign :: Maybe Timestamp -> Foreign
maybeTimestampToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)
  Just (Timestamp ts) -> unsafeToForeign ts

-- | Maybe String を Foreign に変換
maybeStringToForeign :: Maybe String -> Foreign
maybeStringToForeign = case _ of
  Nothing -> unsafeToForeign (unit :: Unit)
  Just s -> unsafeToForeign s

-- | DB 行を Obligation に変換
rowToObligation :: Foreign -> Obligation
rowToObligation row =
  { id: unsafeFromForeign (getField row "id")
  , kind: stringToObligationKind (unsafeFromForeign (getField row "kind"))
  , debtor: mkSubjectId (unsafeFromForeign (getField row "debtor"))
  , creditor: mkSubjectId (unsafeFromForeign (getField row "creditor"))
  , thingRef: Nothing  -- TODO: NULL 判定
  , amount: Nothing  -- TODO: NULL 判定
  , dueDate: Nothing  -- TODO: NULL 判定
  , status: stringToObligationStatus (unsafeFromForeign (getField row "status"))
  }

-- | DB 行を ContractRelation に変換
rowToContractRelation :: Foreign -> ContractRelation
rowToContractRelation row =
  { from: mkContractId (unsafeFromForeign (getField row "from_contract"))
  , to: mkContractId (unsafeFromForeign (getField row "to_contract"))
  , kind: stringToContractRelationKind (unsafeFromForeign (getField row "kind"))
  , description: Nothing  -- TODO: NULL 判定
  }
