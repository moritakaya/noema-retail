-- | Gateway.Yahoo
-- |
-- | Yahoo!ショッピング API との連携アダプター。
-- |
-- | 認証: OAuth2（リフレッシュトークンでアクセストークン取得）
-- | API: https://circus.shopping.yahooapis.jp/ShoppingWebService/V1/
module Gateway.Yahoo
  ( YahooAdapter
  , YahooConfig
  , TokenCache
  , mkYahooAdapter
  , getStockYahoo
  , setStockYahoo
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (toNullable)
import Data.String (split, Pattern(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Foreign.Object as Object
import Noema.Topos.Situs (ThingId(..), Quantity(..))
import Gateway.InventoryAdapter (StockInfo)
import Noema.Horizont.Carrier (CarrierError(..))
import Platform.Cloudflare.FFI.Fetch (fetchWithInit)
import Platform.Cloudflare.FFI.Response (status, ok, text)

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
getAccessToken :: YahooAdapter -> Aff (Either CarrierError String)
getAccessToken adapter = do
  cached <- liftEffect $ Ref.read adapter.tokenCache
  now <- getCurrentTime
  case cached of
    Just cache | cache.expiresAt > now + 60000.0 ->
      pure $ Right cache.accessToken
    _ -> refreshAccessToken adapter

-- | アクセストークンをリフレッシュ
refreshAccessToken :: YahooAdapter -> Aff (Either CarrierError String)
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
      _ <- text response
      -- TODO: JSON パースして access_token と expires_in を取得
      let token = "mock_token"  -- 仮実装
          expiresIn = 3600.0
      now <- getCurrentTime
      liftEffect $ Ref.write (Just { accessToken: token, expiresAt: now + expiresIn * 1000.0 }) adapter.tokenCache
      pure $ Right token
    else do
      errText <- text response
      pure $ Left $ AuthenticationError errText

-- | productId を itemCode と subCode に分割
parseProductId :: String -> { itemCode :: String, subCode :: String }
parseProductId productId =
  case split (Pattern ":") productId of
    [itemCode, subCode] -> { itemCode, subCode }
    _ -> { itemCode: productId, subCode: "" }

-- | Carrier インスタンス（手動実装）
getStockYahoo :: YahooAdapter -> ThingId -> Aff (Either CarrierError StockInfo)
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
          _ <- text response
          -- TODO: XML/JSON パース
          pure $ Right
            { productId
            , quantity: 0
            , lastUpdated: Nothing
            }
        else do
          errText <- text response
          pure $ Left $ ApiError (status response) errText

setStockYahoo :: YahooAdapter -> ThingId -> Quantity -> Aff (Either CarrierError Unit)
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

--------------------------------------------------------------------------------
-- ヘルパー
--------------------------------------------------------------------------------

foreign import getCurrentTime :: Aff Number
