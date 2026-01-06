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
-- | > Cognition を通じて事実へと崩落する。
module Workers.Attractor.InventoryAttractor
  ( InventoryAttractorState
  , createAttractor
  , handleFetch
  , handleAlarm
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Exception (try)
import Foreign (Foreign, unsafeToForeign)
import Foreign.Object as Object
import Noema.Domain.Base (ThingId(..), LocationId(..), mkTimestamp)
import Noema.Domain.Inventory
  ( Inventory(..)
  , Quantity(..)
  , QuantityDelta(..)
  , InventoryEventType(..)
  , InventoryF(..)
  , Channel
  , channelFromString
  )
import Noema.Handler.InventoryHandler (InventoryEnv, mkInventoryEnv, initializeSchema, runInventoryIntent)
import Noema.Intent.Freer (Intent, liftIntent)
import Workers.FFI.DurableObject (DurableObjectState, DurableObjectStorage, getStorage, getSql, setAlarm)
import Workers.FFI.Request (Request, url, method, json)
import Workers.FFI.Response (Response, newResponseWithInit, jsonResponse, errorResponse, notFoundResponse)
import Workers.FFI.SqlStorage (SqlStorage, exec)

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
-- | Request → Intent → Cognition（Handler） → Response
-- | リクエストは Intent へ変換され、Handler により解釈され、
-- | Response として事実化される。
handleFetch :: InventoryAttractorState -> Request -> Effect Response
handleFetch state' req = do
  state <- ensureInitialized state'
  let reqUrl = url req
      reqMethod = method req

  -- パスを解析
  let path = parseUrlPath reqUrl

  -- ルーティング
  case { method: reqMethod, path } of
    -- GET /inventory/:productId/:locationId
    { method: "GET", path: ["inventory", productId, locationId] } ->
      handleGetInventory state (ThingId productId) (LocationId locationId)

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

handleGetInventory :: InventoryAttractorState -> ThingId -> LocationId -> Effect Response
handleGetInventory state productId locationId = do
  let intent = liftIntent $ GetInventory productId locationId identity
  result <- runInventoryIntent state.env intent
  case result of
    Nothing -> notFoundResponse "Inventory not found"
    Just inv -> jsonResponse $ inventoryToJson inv

handleGetInventoryByProduct :: InventoryAttractorState -> ThingId -> Effect Response
handleGetInventoryByProduct state productId = do
  let intent = liftIntent $ GetInventoryByProduct productId identity
  result <- runInventoryIntent state.env intent
  jsonResponse $ inventoryToJson <$> result

handleCreateInventory :: InventoryAttractorState -> Request -> Effect Response
handleCreateInventory state req = do
  -- TODO: JSON パース
  let productId = ThingId "default"
      locationId = LocationId "default"
      quantity = Quantity 0
  let intent = liftIntent $ CreateInventory productId locationId quantity identity
  result <- runInventoryIntent state.env intent
  jsonResponse $ inventoryToJson result

handleAdjustStock :: InventoryAttractorState -> Request -> Effect Response
handleAdjustStock state req = do
  -- TODO: JSON パース
  let productId = ThingId "default"
      locationId = LocationId "default"
      delta = QuantityDelta 0
      eventType = IETAdjust
      channel = channelFromString "self_ec"
      refId = ""
  let intent = liftIntent $ AdjustStock productId locationId delta eventType channel refId identity
  result <- runInventoryIntent state.env intent
  jsonResponse $ inventoryToJson result

handleReserveStock :: InventoryAttractorState -> Request -> Effect Response
handleReserveStock state req = do
  -- TODO: JSON パース
  let productId = ThingId "default"
      locationId = LocationId "default"
      quantity = Quantity 1
      channel = channelFromString "self_ec"
      orderId = Nothing
  let intent = liftIntent $ ReserveStock productId locationId quantity channel orderId identity
  result <- runInventoryIntent state.env intent
  case result of
    Nothing -> errorResponse 400 "Insufficient stock"
    Just reservationId -> jsonResponse { reservationId: unwrap reservationId }

handleReleaseReservation :: InventoryAttractorState -> String -> Effect Response
handleReleaseReservation state reservationId = do
  let intent = liftIntent $ ReleaseReservation (wrap reservationId) identity
  result <- runInventoryIntent state.env intent
  jsonResponse { success: result }
  where
    wrap s = unsafeCoerce s

handleGetSyncStatus :: InventoryAttractorState -> ThingId -> Effect Response
handleGetSyncStatus state productId = do
  let intent = liftIntent $ GetSyncStatus productId identity
  result <- runInventoryIntent state.env intent
  jsonResponse result

handleGetInventoryLog :: InventoryAttractorState -> ThingId -> Effect Response
handleGetInventoryLog state productId = do
  let from = mkTimestamp 0.0
      to = mkTimestamp 9999999999999.0
  let intent = liftIntent $ GetInventoryLog productId from to identity
  result <- runInventoryIntent state.env intent
  jsonResponse result

--------------------------------------------------------------------------------
-- ヘルパー関数
--------------------------------------------------------------------------------

-- | URL パスを解析
foreign import parseUrlPath :: String -> Array String

-- | Inventory を JSON に変換
inventoryToJson :: Inventory -> Foreign
inventoryToJson (Inventory inv) = unsafeToForeign
  { id: unwrap inv.id
  , productId: unwrap inv.productId
  , locationId: unwrap inv.locationId
  , quantity: unwrap inv.quantity
  , reserved: unwrap inv.reserved
  , updatedAt: unwrap inv.updatedAt
  }

-- | 安全でない型変換（一時的）
foreign import unsafeCoerce :: forall a b. a -> b
