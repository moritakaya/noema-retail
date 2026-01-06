-- | Noema Adapter: SmaregiAdapter
-- |
-- | スマレジ Platform API との連携アダプター。
-- |
-- | 認証: Bearer token
-- | API: https://api.smaregi.jp/
module Noema.Presheaf.SmaregiAdapter
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
import Noema.Vorzeichnung.Vocabulary.Base (ThingId(..), Timestamp)
import Noema.Vorzeichnung.Vocabulary.InventoryF
  ( Channel(..)
  , Quantity(..)
  , SyncResult(..)
  )
import Noema.Presheaf.ChannelAdapter
  ( class ChannelAdapter
  , getStock
  , setStock
  , AdapterError(..)
  )
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

-- | ChannelAdapter インスタンス
instance ChannelAdapter SmaregiAdapter where
  channel _ = ChannelSmaregi

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
    now <- currentTimestamp'
    result <- getStock adapter productId
    case result of
      Left err -> pure $ SyncFailure
        { channel: ChannelSmaregi
        , error: show err
        , timestamp: now
        }
      Right stockInfo -> pure $ SyncSuccess
        { channel: ChannelSmaregi
        , quantitySynced: Quantity stockInfo.quantity
        , timestamp: now
        }

  syncFromNoema adapter productId quantity = do
    now <- currentTimestamp'
    result <- setStock adapter productId quantity
    case result of
      Left err -> pure $ SyncFailure
        { channel: ChannelSmaregi
        , error: show err
        , timestamp: now
        }
      Right _ -> pure $ SyncSuccess
        { channel: ChannelSmaregi
        , quantitySynced: quantity
        , timestamp: now
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
