-- | Noema Retail: Main Entry Point
-- |
-- | Cloudflare Workers のエントリーポイント。
-- |
-- | 哲学的基盤：
-- | > プログラムとは、主体が世界に対して投げかける意志を、
-- | > Vorzeichnungsschema として構造化し、認知（Cognition）による
-- | > 忘却を通じて事実へと崩落させる、対話的運動である。
-- |
-- | このモジュールは、外部からのリクエストを Intent に変換し、
-- | 適切な Attractor へルーティングする役割を担う。
module Main where

import Prelude

import Data.Array (uncons, drop)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Platform.Cloudflare.FFI.Request (Request, url, method)
import Platform.Cloudflare.FFI.Response (Response, newResponseWithInit, jsonResponse, errorResponse)
import Platform.Cloudflare.FFI.DurableObject (DurableObjectState, DurableObjectNamespace, Env, idFromName, get, fetch)
import Platform.Cloudflare.InventoryAttractor as InventoryAttractor
import Foreign.Object as Object

-- | Worker fetch ハンドラー
-- |
-- | 圏論的解釈：
-- | Request → Durable Object Stub → Response
-- | リクエストは適切な Attractor へルーティングされ、
-- | 処理結果が Response として返される。
handleFetch :: Env -> Request -> Aff Response
handleFetch env req = do
  let reqUrl = url req
      reqMethod = method req
      path = parseUrlPath reqUrl

  -- ルーティング
  case uncons path of
    -- Health check
    Nothing -> liftEffect $ jsonResponse { status: "ok", service: "noema-retail" }

    -- API routes → InventoryAttractor へ委譲
    Just { head: "api", tail: rest } -> do
      -- Durable Object に委譲
      let namespace = getInventoryNamespace env
      doId <- liftEffect $ idFromName namespace "main"
      stub <- liftEffect $ get namespace doId
      -- 内部 URL に変換してフォワード
      internalReq <- liftEffect $ createInternalRequest rest req
      fetch stub internalReq

    -- 404
    _ -> liftEffect $ errorResponse 404 "Not found"

-- | Scheduled ハンドラー（Cron Trigger）
-- |
-- | 5分毎に実行され、チャネル同期を行う。
handleScheduled :: Env -> Effect Unit
handleScheduled env = do
  log "Running scheduled sync..."
  -- TODO: チャネル同期ロジック
  pure unit

--------------------------------------------------------------------------------
-- Durable Object クラス
--------------------------------------------------------------------------------

-- | InventoryAttractor Durable Object
-- |
-- | PureScript から Cloudflare Workers ランタイムへエクスポートされる。
foreign import data InventoryAttractorClass :: Type

-- | Durable Object クラスを作成
createInventoryAttractorClass :: Effect InventoryAttractorClass
createInventoryAttractorClass = _createDOClass
  { create: InventoryAttractor.createAttractor
  , fetch: \state req -> InventoryAttractor.handleFetch state req
  , alarm: \state -> InventoryAttractor.handleAlarm state
  }

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

foreign import parseUrlPath :: String -> Array String
foreign import getInventoryNamespace :: Env -> DurableObjectNamespace
foreign import createInternalRequest :: Array String -> Request -> Effect Request
foreign import _createDOClass :: forall state.
  { create :: DurableObjectState -> Effect state
  , fetch :: state -> Request -> Effect Response
  , alarm :: state -> Effect Unit
  } -> Effect InventoryAttractorClass

--------------------------------------------------------------------------------
-- エクスポート
--------------------------------------------------------------------------------

-- | Worker エントリーポイント
-- |
-- | Cloudflare Workers ランタイムから呼び出される。
main :: Effect Unit
main = do
  log "Noema Retail Worker initialized"
  pure unit
