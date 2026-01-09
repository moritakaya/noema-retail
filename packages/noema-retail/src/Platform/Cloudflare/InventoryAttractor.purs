-- | Noema Workers: InventoryAttractor
-- |
-- | 在庫管理の Durable Object 実装。
-- |
-- | 圏論的解釈：
-- | Attractor は A-algebra として機能する：
-- | - Presheaf G: 在庫状態（SQLite に永続化）
-- | - α: InventoryF ∘ G ⇒ G（状態更新）
-- |
-- | 哲学的基盤：
-- | > Attractor は世界の状態を引き寄せ、保持する。
-- | > Intent は Attractor に向かって投げかけられ、
-- | > Interpretation（解釈）を通じて Factum（事実）へと崩落する。
-- |
-- | ## Factum と Effect の境界
-- |
-- | Attractor のエントリーポイント（handleFetch, handleAlarm）は
-- | 外界との境界であるため Effect を返す。
-- | 内部では Factum を使用し、collapse で Effect に変換する。
-- |
-- | > 実行とは忘却である。
module Platform.Cloudflare.InventoryAttractor
  ( InventoryAttractorState
  , createAttractor
  , handleFetch
  , handleAlarm
  ) where

import Prelude

import Data.Newtype (unwrap)
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign)
import Noema.Topos.Situs
  ( ThingId(..)
  , SubjectId
  , Quantity(..)
  , QuantityDelta(..)
  , mkSubjectId
  , unwrapSubjectId
  , unwrapThingId
  )
import Noema.Vorzeichnung.Vocabulary.InventoryF
  ( StockInfo
  , getStock
  , setStock
  , adjustStock
  , reserveStock
  , releaseReservation
  )
import Noema.Cognition.InventoryInterpretation (InventoryEnv, mkInventoryEnv, initializeSchema, runInventoryIntent, exec)
import Noema.Sedimentation.Factum (collapse, recognize)
import Platform.Cloudflare.FFI.DurableObject (DurableObjectState, DurableObjectStorage, getStorage, getSql)
import Platform.Cloudflare.FFI.Request (Request, url, method)
import Platform.Cloudflare.FFI.Response (Response, jsonResponse, errorResponse, notFoundResponse)

-- | Attractor の内部状態
type InventoryAttractorState =
  { env :: InventoryEnv
  , storage :: DurableObjectStorage
  , initialized :: Boolean
  }

-- | Attractor を作成
createAttractor :: DurableObjectState -> Effect InventoryAttractorState
createAttractor ctx = do
  let storage = getStorage ctx
      sql = getSql storage
      env = mkInventoryEnv sql
  pure
    { env
    , storage
    , initialized: false
    }

-- | スキーマを初期化（必要な場合のみ）
ensureInitialized :: InventoryAttractorState -> Effect InventoryAttractorState
ensureInitialized state
  | state.initialized = pure state
  | otherwise = do
      initializeSchema state.env.sql
      -- 1分後にアラームを設定（期限切れ予約のクリーンアップ用）
      -- setAlarm state.storage (60000.0)
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
handleFetch :: InventoryAttractorState -> Request -> Effect Response
handleFetch state' req = do
  state <- ensureInitialized state'
  let reqUrl = url req
      reqMethod = method req

  -- パスを解析
  let path = parseUrlPath reqUrl

  -- ルーティング
  case { method: reqMethod, path } of
    -- GET /inventory/:productId/:subjectId
    -- 注: URL パスは locationId のまま（後方互換性）、
    -- 内部では SubjectId として扱う
    { method: "GET", path: ["inventory", productId, subjectIdStr] } ->
      handleGetInventory state (ThingId productId) (mkSubjectId subjectIdStr)

    -- GET /inventory/:productId
    { method: "GET", path: ["inventory", productId] } ->
      handleGetInventoryByProduct state (ThingId productId)

    -- POST /inventory
    { method: "POST", path: ["inventory"] } ->
      handleCreateInventory state req

    -- POST /adjust
    { method: "POST", path: ["adjust"] } ->
      handleAdjustStock state req

    -- POST /reserve
    { method: "POST", path: ["reserve"] } ->
      handleReserveStock state req

    -- DELETE /reserve/:reservationId
    { method: "DELETE", path: ["reserve", reservationId] } ->
      handleReleaseReservation state reservationId

    -- GET /sync/:productId
    { method: "GET", path: ["sync", productId] } ->
      handleGetSyncStatus state (ThingId productId)

    -- GET /log/:productId
    { method: "GET", path: ["log", productId] } ->
      handleGetInventoryLog state (ThingId productId)

    -- 404 Not Found
    _ -> notFoundResponse "Not found"

-- | アラームを処理（期限切れ予約のクリーンアップ）
handleAlarm :: InventoryAttractorState -> Effect Unit
handleAlarm state = do
  -- 期限切れの予約を削除
  let _ = exec state.env.sql
        """
        DELETE FROM reservation
        WHERE expires_at < ?
        """
  -- 次のアラームを設定
  -- setAlarm state.storage (60000.0)
  pure unit

--------------------------------------------------------------------------------
-- ルートハンドラー
--------------------------------------------------------------------------------

-- | 各ルートハンドラーでは:
-- | 1. Intent を構築
-- | 2. runInventoryIntent で Factum を取得
-- | 3. collapse で Effect に崩落（外界との境界）

handleGetInventory :: InventoryAttractorState -> ThingId -> SubjectId -> Effect Response
handleGetInventory state productId subjectId = collapse do
  let intent = getStock productId subjectId
  result <- runInventoryIntent state.env intent unit
  recognize $ jsonResponse $ stockInfoToJson result

handleGetInventoryByProduct :: InventoryAttractorState -> ThingId -> Effect Response
handleGetInventoryByProduct state productId = collapse do
  -- 新しい API では subject が必須のため、デフォルト subject を使用
  let intent = getStock productId (mkSubjectId "default")
  result <- runInventoryIntent state.env intent unit
  recognize $ jsonResponse [ stockInfoToJson result ]

handleCreateInventory :: InventoryAttractorState -> Request -> Effect Response
handleCreateInventory state _req = collapse do
  -- TODO: JSON パース
  let productId = ThingId "default"
      subjectId = mkSubjectId "default"
      quantity = Quantity 0
  let intent = setStock productId subjectId quantity
  _ <- runInventoryIntent state.env intent unit
  -- setStock は Unit を返すため、作成後に取得
  let getIntent = getStock productId subjectId
  result <- runInventoryIntent state.env getIntent unit
  recognize $ jsonResponse $ stockInfoToJson result

handleAdjustStock :: InventoryAttractorState -> Request -> Effect Response
handleAdjustStock state _req = collapse do
  -- TODO: JSON パース
  let productId = ThingId "default"
      subjectId = mkSubjectId "default"
      delta = QuantityDelta 0
  let intent = adjustStock productId subjectId delta
  _newQty <- runInventoryIntent state.env intent unit
  -- adjustStock は新しい Quantity を返す。StockInfo として取得して返す
  let getIntent = getStock productId subjectId
  stockInfo <- runInventoryIntent state.env getIntent unit
  recognize $ jsonResponse $ stockInfoToJson stockInfo

handleReserveStock :: InventoryAttractorState -> Request -> Effect Response
handleReserveStock state _req = collapse do
  -- TODO: JSON パース
  let productId = ThingId "default"
      subjectId = mkSubjectId "default"
      quantity = Quantity 1
  let intent = reserveStock productId subjectId quantity
  result <- runInventoryIntent state.env intent unit
  if result
    then recognize $ jsonResponse { success: true, message: "Reserved successfully" }
    else recognize $ errorResponse 400 "Insufficient stock"

handleReleaseReservation :: InventoryAttractorState -> String -> Effect Response
handleReleaseReservation state reservationId = collapse do
  -- TODO: reservationId から productId/subjectId を取得するロジックが必要
  let productId = ThingId "default"
      subjectId = mkSubjectId "default"
  let intent = releaseReservation productId subjectId reservationId
  _ <- runInventoryIntent state.env intent unit
  recognize $ jsonResponse { success: true }

handleGetSyncStatus :: InventoryAttractorState -> ThingId -> Effect Response
handleGetSyncStatus _state _productId = do
  -- TODO: 同期状態取得は新しい Arrow API では未実装
  jsonResponse { status: "not_implemented", message: "Sync status not available in Arrow-based API" }

handleGetInventoryLog :: InventoryAttractorState -> ThingId -> Effect Response
handleGetInventoryLog _state _productId = do
  -- TODO: ログ取得は新しい Arrow API では未実装
  jsonResponse { logs: ([] :: Array String), message: "Inventory log not available in Arrow-based API" }

--------------------------------------------------------------------------------
-- ヘルパー関数
--------------------------------------------------------------------------------

-- | URL パスを解析
foreign import parseUrlPath :: String -> Array String

-- | StockInfo を JSON に変換
stockInfoToJson :: StockInfo -> Foreign
stockInfoToJson info = unsafeToForeign
  { thingId: unwrapThingId info.thingId
  , subjectId: unwrapSubjectId info.subjectId
  , quantity: unwrap info.quantity
  , reserved: unwrap info.reserved
  , available: unwrap info.available
  }
