-- | Noema Adapter: YahooAdapter
-- |
-- | Yahoo!ショッピング API との連携アダプター。
-- |
-- | 認証: OAuth2（リフレッシュトークンでアクセストークン取得）
-- | API: https://circus.shopping.yahooapis.jp/ShoppingWebService/V1/
module Adapter.YahooAdapter
  ( YahooAdapter
  , YahooConfig
  , mkYahooAdapter
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (toNullable)
import Data.String (split, Pattern(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Foreign.Object as Object
import Noema.Domain.Base (ThingId(..), Timestamp, mkTimestamp)
import Noema.Domain.Inventory
  ( Channel(..)
  , Quantity(..)
  , SyncResult(..)
  , InventoryEvent
  )
import Adapter.ChannelAdapter
  ( class ChannelAdapter
  , AdapterError(..)
  , StockInfo
  )
import Workers.FFI.Fetch (fetchWithInit)
import Workers.FFI.Response (Response, status, ok, text)

-- | Yahoo アダプター設定
type YahooConfig =
  { sellerId :: String
  , clientId :: String
  , clientSecret :: String
  , refreshToken :: String
  , publicKey :: String
  , publicKeyVersion :: Int
  , publicKeyExpiry :: Number  -- Unix ミリ秒
  }

-- | トークンキャッシュ
type TokenCache =
  { accessToken :: String
  , expiresAt :: Number
  }

-- | Yahoo アダプター
type YahooAdapter =
  { config :: YahooConfig
  , tokenCache :: Ref (Maybe TokenCache)
  }

-- | アダプターを作成
mkYahooAdapter :: YahooConfig -> Effect YahooAdapter
mkYahooAdapter config = do
  tokenCache <- Ref.new Nothing
  pure { config, tokenCache }

-- | アクセストークンを取得（キャッシュ付き）
getAccessToken :: YahooAdapter -> Aff (Either AdapterError String)
getAccessToken adapter = do
  cached <- liftEffect $ Ref.read adapter.tokenCache
  now <- getCurrentTime
  case cached of
    Just cache | cache.expiresAt > now + 60000.0 ->
      pure $ Right cache.accessToken
    _ -> refreshAccessToken adapter

-- | アクセストークンをリフレッシュ
refreshAccessToken :: YahooAdapter -> Aff (Either AdapterError String)
refreshAccessToken adapter = do
  let config = adapter.config
      url = "https://auth.login.yahoo.co.jp/yconnect/v2/token"
      body = "grant_type=refresh_token"
             <> "&client_id=" <> config.clientId
             <> "&client_secret=" <> config.clientSecret
             <> "&refresh_token=" <> config.refreshToken
  response <- fetchWithInit url
    { method: "POST"
    , headers: Object.fromFoldable
        [ "Content-Type" /\ "application/x-www-form-urlencoded"
        ]
    , body: toNullable (Just body)
    }
  if ok response
    then do
      bodyText <- text response
      -- TODO: JSON パースして access_token と expires_in を取得
      let token = "mock_token"  -- 仮実装
          expiresIn = 3600.0
      now <- getCurrentTime
      liftEffect $ Ref.write (Just { accessToken: token, expiresAt: now + expiresIn * 1000.0 }) adapter.tokenCache
      pure $ Right token
    else do
      bodyText <- text response
      pure $ Left $ AuthenticationError bodyText

-- | productId を itemCode と subCode に分割
parseProductId :: String -> { itemCode :: String, subCode :: String }
parseProductId productId =
  case split (Pattern ":") productId of
    [itemCode, subCode] -> { itemCode, subCode }
    _ -> { itemCode: productId, subCode: "" }

-- | ChannelAdapter インスタンス（手動実装）
getStockYahoo :: YahooAdapter -> ThingId -> Aff (Either AdapterError StockInfo)
getStockYahoo adapter (ThingId productId) = do
  tokenResult <- getAccessToken adapter
  case tokenResult of
    Left err -> pure $ Left err
    Right token -> do
      let { itemCode, subCode } = parseProductId productId
          url = "https://circus.shopping.yahooapis.jp/ShoppingWebService/V1/getStock"
          body = "seller_id=" <> adapter.config.sellerId
                 <> "&item_code=" <> itemCode
                 <> "&sub_code=" <> subCode
      response <- fetchWithInit url
        { method: "POST"
        , headers: Object.fromFoldable
            [ "Authorization" /\ ("Bearer " <> token)
            , "Content-Type" /\ "application/x-www-form-urlencoded"
            ]
        , body: toNullable (Just body)
        }
      if ok response
        then do
          bodyText <- text response
          -- TODO: XML/JSON パース
          pure $ Right
            { productId
            , quantity: 0
            , lastUpdated: Nothing
            }
        else do
          bodyText <- text response
          pure $ Left $ ApiError (status response) bodyText

setStockYahoo :: YahooAdapter -> ThingId -> Quantity -> Aff (Either AdapterError Unit)
setStockYahoo adapter (ThingId productId) (Quantity qty) = do
  tokenResult <- getAccessToken adapter
  case tokenResult of
    Left err -> pure $ Left err
    Right token -> do
      let { itemCode, subCode } = parseProductId productId
          url = "https://circus.shopping.yahooapis.jp/ShoppingWebService/V1/setStock"
          body = "seller_id=" <> adapter.config.sellerId
                 <> "&item_code=" <> itemCode
                 <> "&sub_code=" <> subCode
                 <> "&quantity=" <> show qty
      response <- fetchWithInit url
        { method: "POST"
        , headers: Object.fromFoldable
            [ "Authorization" /\ ("Bearer " <> token)
            , "Content-Type" /\ "application/x-www-form-urlencoded"
            ]
        , body: toNullable (Just body)
        }
      if ok response
        then pure $ Right unit
        else do
          bodyText <- text response
          pure $ Left $ ApiError (status response) bodyText

syncToNoemaYahoo :: YahooAdapter -> ThingId -> Aff SyncResult
syncToNoemaYahoo adapter productId = do
  result <- getStockYahoo adapter productId
  case result of
    Left err -> pure $ SyncFailure
      { channel: ChannelYahoo
      , error: show err
      , timestamp: mkTimestamp 0.0
      }
    Right stockInfo -> pure $ SyncSuccess
      { channel: ChannelYahoo
      , quantitySynced: Quantity stockInfo.quantity
      , timestamp: mkTimestamp 0.0
      }

syncFromNoemaYahoo :: YahooAdapter -> ThingId -> Quantity -> Aff SyncResult
syncFromNoemaYahoo adapter productId quantity = do
  result <- setStockYahoo adapter productId quantity
  case result of
    Left err -> pure $ SyncFailure
      { channel: ChannelYahoo
      , error: show err
      , timestamp: mkTimestamp 0.0
      }
    Right _ -> pure $ SyncSuccess
      { channel: ChannelYahoo
      , quantitySynced: quantity
      , timestamp: mkTimestamp 0.0
      }

processOrdersYahoo :: YahooAdapter -> Timestamp -> Aff { processed :: Int, errors :: Array String, events :: Array InventoryEvent }
processOrdersYahoo adapter since = do
  -- TODO: 注文 API で注文を取得し、在庫イベントに変換
  pure { processed: 0, errors: [], events: [] }

--------------------------------------------------------------------------------
-- ヘルパー
--------------------------------------------------------------------------------

foreign import getCurrentTime :: Aff Number

-- | タプル演算子
infixr 6 Tuple as /\

data Tuple a b = Tuple a b
