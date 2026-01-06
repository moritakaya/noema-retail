-- | Noema Adapter: RakutenAdapter
-- |
-- | 楽天市場 RMS API との連携アダプター。
-- |
-- | 認証: ESA（serviceSecret:licenseKey を Base64 エンコード）
-- | API: https://api.rms.rakuten.co.jp/es/2.0/
module Noema.Presheaf.RakutenAdapter
  ( RakutenAdapter
  , RakutenConfig
  , mkRakutenAdapter
  , getAuthHeader
  , isLicenseExpired
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (toNullable)
import Data.String (split, Pattern(..))
import Data.Tuple.Nested ((/\))
import Foreign.Object as Object
import Noema.Vorzeichnung.Vocabulary.Base (ThingId(..), mkTimestamp)
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
import Platform.Cloudflare.FFI.Crypto (base64Encode)

-- | 楽天アダプター設定
type RakutenConfig =
  { shopUrl :: String
  , serviceSecret :: String
  , licenseKey :: String
  , licenseExpiry :: Number  -- Unix ミリ秒
  }

-- | 楽天アダプター
newtype RakutenAdapter = RakutenAdapter RakutenConfig

-- | アダプターを作成
mkRakutenAdapter :: RakutenConfig -> RakutenAdapter
mkRakutenAdapter = RakutenAdapter

-- | ESA 認証ヘッダーを生成
getAuthHeader :: RakutenConfig -> String
getAuthHeader config =
  let credentials = config.serviceSecret <> ":" <> config.licenseKey
  in "ESA " <> base64Encode credentials

-- | ライセンスキーが期限切れか確認
isLicenseExpired :: RakutenConfig -> Number -> Boolean
isLicenseExpired config now = now > config.licenseExpiry

-- | productId を manageNumber と variantId に分割
parseProductId :: String -> { manageNumber :: String, variantId :: String }
parseProductId productId =
  case split (Pattern ":") productId of
    [manageNumber, variantId] -> { manageNumber, variantId }
    _ -> { manageNumber: productId, variantId: "default" }

-- | ChannelAdapter インスタンス
instance ChannelAdapter RakutenAdapter where
  channel _ = ChannelRakuten

  getStock (RakutenAdapter config) (ThingId productId) = do
    let { manageNumber, variantId } = parseProductId productId
        url = "https://api.rms.rakuten.co.jp/es/2.0/inventories/manage-numbers/"
              <> manageNumber <> "/variants/" <> variantId
    response <- fetchWithInit url
      { method: "GET"
      , headers: Object.fromFoldable
          [ "Authorization" /\ getAuthHeader config
          , "Content-Type" /\ "application/json; charset=utf-8"
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

  setStock (RakutenAdapter config) (ThingId productId) (Quantity qty) = do
    let { manageNumber, variantId } = parseProductId productId
        url = "https://api.rms.rakuten.co.jp/es/2.0/inventories/bulk-upsert"
        body = """{"inventories":[{"manageNumber":""" <> "\"" <> manageNumber <> "\"" <>
               ""","variants":[{"variantId":""" <> "\"" <> variantId <> "\"" <>
               ""","inventory":{"quantity":""" <> show qty <> "}}]}]}"
    response <- fetchWithInit url
      { method: "POST"
      , headers: Object.fromFoldable
          [ "Authorization" /\ getAuthHeader config
          , "Content-Type" /\ "application/json; charset=utf-8"
          ]
      , body: toNullable (Just body)
      }
    if ok response
      then pure $ Right unit
      else do
        bodyText <- text response
        pure $ Left $ ApiError (status response) bodyText

  syncToNoema adapter productId = do
    result <- getStock adapter productId
    case result of
      Left err -> pure $ SyncFailure
        { channel: ChannelRakuten
        , error: show err
        , timestamp: mkTimestamp 0.0  -- TODO: 現在時刻
        }
      Right stockInfo -> pure $ SyncSuccess
        { channel: ChannelRakuten
        , quantitySynced: Quantity stockInfo.quantity
        , timestamp: mkTimestamp 0.0
        }

  syncFromNoema adapter productId quantity = do
    result <- setStock adapter productId quantity
    case result of
      Left err -> pure $ SyncFailure
        { channel: ChannelRakuten
        , error: show err
        , timestamp: mkTimestamp 0.0
        }
      Right _ -> pure $ SyncSuccess
        { channel: ChannelRakuten
        , quantitySynced: quantity
        , timestamp: mkTimestamp 0.0
        }

  processOrders (RakutenAdapter _config) _since = do
    -- TODO: 楽天ペイ受注API で注文を取得し、在庫イベントに変換
    pure { processed: 0, errors: [], events: [] }
