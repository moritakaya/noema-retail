-- | Noema Workers: SubjectAttractor
-- |
-- | 主体（Subject）管理の Durable Object 実装。
-- |
-- | 圏論的解釈：
-- | Attractor は A-algebra として機能する：
-- | - Presheaf G: 主体状態（SQLite に永続化）
-- | - α: SubjectF ∘ G ⇒ G（状態更新）
-- |
-- | 哲学的基盤：
-- | > Subject は意志を持つ主体。Thing を「包摂」する。
-- | > Subject の World（法座標）が、包摂された Thing の解釈を規定する。
-- |
-- | ## Subject と Thing の関係
-- |
-- | - Subject: 意志を持つ主体（DO として実装）
-- | - Thing: 意志を持たない物（Subject に包摂される）
-- | - 包摂関係: Thing.situs :: SubjectId
-- |
-- | ## Factum と Effect の境界
-- |
-- | Attractor のエントリーポイント（handleFetch, handleAlarm）は
-- | 外界との境界であるため Effect を返す。
-- | 内部では Factum を使用し、collapse で Effect に変換する。
-- |
-- | > 実行とは忘却である。
module Platform.Cloudflare.SubjectAttractor
  ( SubjectAttractorState
  , createAttractor
  , handleFetch
  , handleAlarm
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign)
import Noema.Topos.Situs
  ( SubjectId
  , Timestamp(..)
  , mkSubjectId
  , unwrapSubjectId
  )
import Noema.Topos.Nomos
  ( World
  , NomosVersion(..)
  , mkWorld
  )
import Noema.Vorzeichnung.Vocabulary.SubjectF
  ( SubjectKind(..)
  , SubjectState
  , SubjectInit
  , SubjectPatch
  , createSubject
  , getSubject
  , getSubjectsByKind
  , updateSubject
  )
import Noema.Cognition.SubjectInterpretation
  ( SubjectEnv
  , mkSubjectEnv
  , initializeSubjectSchema
  , runSubjectIntent
  )
import Noema.Sedimentation.Factum (Factum, collapse, recognize)
import Platform.Cloudflare.FFI.DurableObject (DurableObjectState, DurableObjectStorage, getStorage, getSql)
import Platform.Cloudflare.FFI.Request (Request, url, method)
import Platform.Cloudflare.FFI.Response (Response, jsonResponse, errorResponse, notFoundResponse)

-- | Attractor の内部状態
type SubjectAttractorState =
  { env :: SubjectEnv
  , storage :: DurableObjectStorage
  , initialized :: Boolean
  }

-- | Attractor を作成
createAttractor :: DurableObjectState -> Effect SubjectAttractorState
createAttractor ctx = do
  let storage = getStorage ctx
      sql = getSql storage
      env = mkSubjectEnv sql
  pure
    { env
    , storage
    , initialized: false
    }

-- | スキーマを初期化（必要な場合のみ）
ensureInitialized :: SubjectAttractorState -> Effect SubjectAttractorState
ensureInitialized state
  | state.initialized = pure state
  | otherwise = do
      initializeSubjectSchema state.env.sql
      pure state { initialized = true }

-- | HTTP リクエストを処理
-- |
-- | 圏論的解釈：
-- | Request → Intent → Interpretation → Factum → Response
-- | リクエストは Intent へ変換され、Interpretation により解釈され、
-- | Factum として事実化される。
-- |
-- | 外界との境界で collapse により Effect へ崩落。
-- | > 実行とは忘却である。
handleFetch :: SubjectAttractorState -> Request -> Effect Response
handleFetch state' req = do
  state <- ensureInitialized state'
  let reqUrl = url req
      reqMethod = method req

  -- パスを解析
  let path = parseUrlPath reqUrl

  -- ルーティング
  case { method: reqMethod, path } of
    -- GET /subject/:subjectId
    { method: "GET", path: ["subject", subjectIdStr] } ->
      handleGetSubject state (mkSubjectId subjectIdStr)

    -- GET /subjects?kind=:kind
    { method: "GET", path: ["subjects"] } ->
      handleGetSubjectsByKind state ThingHolder  -- TODO: クエリパラメータ解析

    -- GET /subjects/kind/:kind
    { method: "GET", path: ["subjects", "kind", kindStr] } ->
      handleGetSubjectsByKindStr state kindStr

    -- POST /subject
    { method: "POST", path: ["subject"] } ->
      handleCreateSubject state req

    -- PATCH /subject/:subjectId
    { method: "PATCH", path: ["subject", subjectIdStr] } ->
      handleUpdateSubject state (mkSubjectId subjectIdStr) req

    -- 404 Not Found
    _ -> notFoundResponse "Not found"

-- | アラームを処理
-- |
-- | Subject 固有の定期処理:
-- | - 非アクティブな Subject の検出
-- | - World 更新の伝播チェック
handleAlarm :: SubjectAttractorState -> Effect Unit
handleAlarm _state = do
  -- TODO: 定期処理の実装
  -- - 長期間非アクティブな Subject の通知
  -- - Nomos バージョン更新の検出
  pure unit

--------------------------------------------------------------------------------
-- ルートハンドラー
--------------------------------------------------------------------------------

-- | 各ルートハンドラーでは:
-- | 1. Intent を構築
-- | 2. runSubjectIntent で Factum を取得
-- | 3. collapse で Effect に崩落（外界との境界）

handleGetSubject :: SubjectAttractorState -> SubjectId -> Effect Response
handleGetSubject state sid = collapse do
  let intent = getSubject sid
  result <- runSubjectIntent state.env intent unit
  recognize $ jsonResponse $ subjectStateToJson result

handleGetSubjectsByKind :: SubjectAttractorState -> SubjectKind -> Effect Response
handleGetSubjectsByKind state kind = collapse do
  let intent = getSubjectsByKind kind
  results <- runSubjectIntent state.env intent unit
  recognize $ jsonResponse $ map subjectStateToJson results

handleGetSubjectsByKindStr :: SubjectAttractorState -> String -> Effect Response
handleGetSubjectsByKindStr state kindStr = do
  let kind = parseSubjectKind kindStr
  handleGetSubjectsByKind state kind

handleCreateSubject :: SubjectAttractorState -> Request -> Effect Response
handleCreateSubject state _req = collapse do
  -- TODO: JSON パース
  let timestamp = Timestamp 0.0  -- TODO: 現在時刻取得
      init :: SubjectInit
      init =
        { kind: ThingHolder
        , world: mkWorld (NomosVersion "1.0.0") timestamp
        }
  let intent = createSubject init
  newSid <- runSubjectIntent state.env intent unit
  -- 作成後に取得して返す
  let getIntent = getSubject newSid
  result <- runSubjectIntent state.env getIntent unit
  recognize $ jsonResponse $ subjectStateToJson result

handleUpdateSubject :: SubjectAttractorState -> SubjectId -> Request -> Effect Response
handleUpdateSubject state sid _req = collapse do
  -- TODO: JSON パース
  let patch :: SubjectPatch
      patch = { world: Nothing }
  let intent = updateSubject sid patch
  _sedimentId <- runSubjectIntent state.env intent unit
  -- 更新後に取得して返す
  let getIntent = getSubject sid
  result <- runSubjectIntent state.env getIntent unit
  recognize $ jsonResponse $ subjectStateToJson result

--------------------------------------------------------------------------------
-- ヘルパー関数
--------------------------------------------------------------------------------

-- | URL パスを解析
foreign import parseUrlPath :: String -> Array String

-- | SubjectKind を文字列から解析
parseSubjectKind :: String -> SubjectKind
parseSubjectKind = case _ of
  "contract_party" -> ContractParty
  "thing_holder" -> ThingHolder
  "system_agent" -> SystemAgent
  _ -> ThingHolder  -- デフォルト

-- | SubjectKind を文字列に変換
showSubjectKind :: SubjectKind -> String
showSubjectKind = case _ of
  ContractParty -> "contract_party"
  ThingHolder -> "thing_holder"
  SystemAgent -> "system_agent"

-- | SubjectState を JSON に変換
subjectStateToJson :: SubjectState -> Foreign
subjectStateToJson state = unsafeToForeign
  { id: unwrapSubjectId state.id
  , kind: showSubjectKind state.kind
  , world: worldToJson state.world
  , lastActivity: unwrap state.lastActivity
  }

-- | World を JSON に変換
worldToJson :: World -> Foreign
worldToJson world = unsafeToForeign
  { nomosVersion: unwrapNomosVersion world.nomosVersion
  , timestamp: unwrap world.timestamp
  , region: world.region
  }

-- | NomosVersion を unwrap
unwrapNomosVersion :: NomosVersion -> String
unwrapNomosVersion (NomosVersion v) = v
