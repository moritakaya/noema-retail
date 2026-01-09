-- | Gateway.Smaregi
-- |
-- | スマレジ Platform API との連携アダプター。
-- |
-- | 認証: Bearer token
-- | API: https://api.smaregi.jp/
module Gateway.Smaregi
  ( SmaregiAdapter
  , SmaregiConfig
  , mkSmaregiAdapter
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (toNullable)
import Data.Tuple.Nested ((/\))
import Effect.Aff (Aff)
import Foreign.Object as Object
import Noema.Topos.Situs (ThingId(..), Quantity(..), Timestamp)
import Gateway.Channel (Channel(..))
import Gateway.InventoryAdapter (class InventoryAdapter, SyncResult(..), getStock, setStock)
import Platform.Cloudflare.Gateway.Adapter (class GatewayAdapter, AdapterError(..))
import Platform.Cloudflare.FFI.Fetch (fetchWithInit)
import Platform.Cloudflare.FFI.Response (status, ok, text)

-- | スマレジアダプター設定
type SmaregiConfig =
  { contractId :: String
  , accessToken :: String
  , storeId :: String
  , apiBaseUrl :: String
  }

-- | スマレジアダプター
newtype SmaregiAdapter = SmaregiAdapter SmaregiConfig

-- | アダプターを作成
mkSmaregiAdapter :: SmaregiConfig -> SmaregiAdapter
mkSmaregiAdapter = SmaregiAdapter

-- | GatewayAdapter インスタンス
instance GatewayAdapter SmaregiAdapter where
  adapterName _ = "Smaregi"
  healthCheck _ = pure $ Right unit

-- | InventoryAdapter インスタンス
instance InventoryAdapter SmaregiAdapter where
  channel _ = Smaregi

  getStock (SmaregiAdapter config) (ThingId productId) = do
    let url = config.apiBaseUrl <> "/pos/stocks?store_id=" <> config.storeId <> "&product_id=" <> productId
    response <- fetchWithInit url
      { method: "GET"
      , headers: Object.fromFoldable
          [ "Authorization" /\ ("Bearer " <> config.accessToken)
          , "Content-Type" /\ "application/json"
          ]
      , body: toNullable Nothing
      }
    if ok response
      then do
        _ <- text response
        -- TODO: JSON パース
        pure $ Right
          { productId
          , quantity: 0
          , lastUpdated: Nothing
          }
      else do
        errText <- text response
        pure $ Left $ ApiError (status response) errText

  setStock (SmaregiAdapter config) (ThingId productId) (Quantity qty) = do
    -- スマレジでは直接在庫を設定できないため、
    -- 差分を計算して入荷/出荷登録を行う
    currentResult <- getStock (SmaregiAdapter config) (ThingId productId)
    case currentResult of
      Left err -> pure $ Left err
      Right current -> do
        let delta = qty - current.quantity
        if delta > 0
          then registerReceipt config productId delta "Noema sync"
          else if delta < 0
            then registerShipment config productId (negate delta) "Noema sync"
            else pure $ Right unit

  syncToNoema adapter productId = do
    result <- getStock adapter productId
    case result of
      Left err -> pure $ SyncFailure
        { channel: Smaregi
        , error: show err
        }
      Right stockInfo -> pure $ SyncSuccess
        { channel: Smaregi
        , quantity: Quantity stockInfo.quantity
        }

  syncFromNoema adapter productId quantity = do
    result <- setStock adapter productId quantity
    case result of
      Left err -> pure $ SyncFailure
        { channel: Smaregi
        , error: show err
        }
      Right _ -> pure $ SyncSuccess
        { channel: Smaregi
        , quantity: quantity
        }

  processOrders (SmaregiAdapter _config) _since = do
    -- TODO: 取引データを取得して在庫イベントに変換
    pure { processed: 0, errors: [], events: [] }

--------------------------------------------------------------------------------
-- 内部ヘルパー
--------------------------------------------------------------------------------

-- | 入荷登録
registerReceipt :: SmaregiConfig -> String -> Int -> String -> Aff (Either AdapterError Unit)
registerReceipt config productId quantity reason = do
  let url = config.apiBaseUrl <> "/pos/stock/receipt"
      body = """{"product_id":""" <> "\"" <> productId <> "\"" <>
             ""","store_id":""" <> "\"" <> config.storeId <> "\"" <>
             ""","quantity":""" <> show quantity <>
             ""","reason":""" <> "\"" <> reason <> "\"}"
  response <- fetchWithInit url
    { method: "POST"
    , headers: Object.fromFoldable
        [ "Authorization" /\ ("Bearer " <> config.accessToken)
        , "Content-Type" /\ "application/json"
        ]
    , body: toNullable (Just body)
    }
  if ok response
    then pure $ Right unit
    else do
      bodyText <- text response
      pure $ Left $ ApiError (status response) bodyText

-- | 出荷登録
registerShipment :: SmaregiConfig -> String -> Int -> String -> Aff (Either AdapterError Unit)
registerShipment config productId quantity reason = do
  let url = config.apiBaseUrl <> "/pos/stock/shipment"
      body = """{"product_id":""" <> "\"" <> productId <> "\"" <>
             ""","store_id":""" <> "\"" <> config.storeId <> "\"" <>
             ""","quantity":""" <> show quantity <>
             ""","reason":""" <> "\"" <> reason <> "\"}"
  response <- fetchWithInit url
    { method: "POST"
    , headers: Object.fromFoldable
        [ "Authorization" /\ ("Bearer " <> config.accessToken)
        , "Content-Type" /\ "application/json"
        ]
    , body: toNullable (Just body)
    }
  if ok response
    then pure $ Right unit
    else do
      bodyText <- text response
      pure $ Left $ ApiError (status response) bodyText

-- | 現在時刻（Aff版）
foreign import currentTimestamp' :: Aff Timestamp
