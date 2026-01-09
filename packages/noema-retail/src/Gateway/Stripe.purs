-- | Gateway.Stripe
-- |
-- | Stripe 決済 API との連携アダプター。
-- |
-- | 認証: API Key (Bearer token)
-- | Webhook: HMAC-SHA256 署名検証
-- | API: https://api.stripe.com/v1/
-- |
-- | 注意: Stripe は在庫管理機能を持たないため、
-- | syncToNoema/syncFromNoema は在庫変更イベントの処理のみ。
module Gateway.Stripe
  ( StripeAdapter
  , StripeConfig
  , ProductMapping
  , mkStripeAdapter
  , verifyWebhookSignature
  , handleWebhook
  , WebhookResult(..)
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (split, Pattern(..), indexOf)
import Data.Array (filter)
import Effect.Aff (Aff)
import Noema.Topos.Situs (ThingId(..))
import Gateway.Channel (Channel(..))
import Gateway.InventoryAdapter (class InventoryAdapter, SyncResult(..), InventoryEvent(..))
import Noema.Horizont.Carrier (class Carrier, CarrierError(..))
import Platform.Cloudflare.FFI.Crypto (hmacSha256, secureCompare)

-- | Stripe アダプター設定
type StripeConfig =
  { apiKey :: String
  , webhookSecret :: String
  , productMappings :: Array ProductMapping  -- Stripe Product ID → Noema Product ID
  }

-- | 商品マッピング
type ProductMapping =
  { stripeProductId :: String
  , stripePriceId :: String
  , noemaProductId :: String
  }

-- | Stripe アダプター
newtype StripeAdapter = StripeAdapter StripeConfig

-- | アダプターを作成
mkStripeAdapter :: StripeConfig -> StripeAdapter
mkStripeAdapter = StripeAdapter

-- | Webhook 処理結果
data WebhookResult
  = WebhookSuccess { events :: Array InventoryEvent }
  | WebhookIgnored String
  | WebhookError String

-- | Webhook 署名を検証
-- |
-- | Stripe の署名形式: t=timestamp,v1=signature
-- | 署名対象: timestamp.payload
verifyWebhookSignature :: StripeConfig -> String -> String -> Aff Boolean
verifyWebhookSignature config payload signature = do
  -- 署名ヘッダーをパース
  let elements = split (Pattern ",") signature
      signatureMap = parseSignatureElements elements
  case lookupTimestamp signatureMap of
    Nothing -> pure false
    Just timestamp -> do
      now <- getCurrentTime
      -- タイムスタンプが5分以内か確認
      if abs (now - timestamp) > 300000.0
        then pure false
        else do
          let signedPayload = show (floor timestamp / 1000.0) <> "." <> payload
          expected <- hmacSha256 signedPayload config.webhookSecret
          let signatures = lookupSignatures signatureMap
          pure $ any (\sig -> secureCompare sig expected) signatures
  where
    parseSignatureElements :: Array String -> Array { key :: String, value :: String }
    parseSignatureElements = map parseElement >>> filter isValid
      where
        parseElement s =
          case indexOf (Pattern "=") s of
            Nothing -> { key: "", value: "" }
            Just idx ->
              { key: take idx s
              , value: drop (idx + 1) s
              }
        isValid { key } = key /= ""

    lookupTimestamp :: Array { key :: String, value :: String } -> Maybe Number
    lookupTimestamp arr =
      case filter (\x -> x.key == "t") arr of
        [{ value }] -> Just $ parseFloat value * 1000.0
        _ -> Nothing

    lookupSignatures :: Array { key :: String, value :: String } -> Array String
    lookupSignatures = filter (\x -> x.key == "v1") >>> map _.value

-- | Webhook を処理
handleWebhook :: StripeAdapter -> String -> String -> Aff WebhookResult
handleWebhook (StripeAdapter config) payload signature = do
  isValid <- verifyWebhookSignature config payload signature
  if not isValid
    then pure $ WebhookError "Invalid signature"
    else do
      -- TODO: JSON パースしてイベントタイプに応じた処理
      -- checkout.session.completed → 在庫減少イベント
      -- charge.refunded → 在庫増加イベント
      pure $ WebhookIgnored "Event type not handled"

-- | Carrier インスタンス
instance Carrier StripeAdapter where
  carrierName _ = "Stripe"
  healthCheck _ = pure $ Right unit

-- | InventoryAdapter インスタンス
instance InventoryAdapter StripeAdapter where
  channel _ = Stripe

  -- Stripe には在庫管理機能がないため、ダミー実装
  getStock _adapter (ThingId _productId) = do
    pure $ Left $ ConfigurationError "Stripe does not support inventory management"

  setStock _adapter _productId _quantity = do
    pure $ Left $ ConfigurationError "Stripe does not support inventory management"

  syncToNoema _adapter _productId = do
    pure $ SyncFailure
      { channel: Stripe
      , error: "Stripe does not support inventory sync"
      }

  syncFromNoema _adapter _productId _quantity = do
    pure $ SyncFailure
      { channel: Stripe
      , error: "Stripe does not support inventory sync"
      }

  -- Webhook 経由で注文を処理
  processOrders (StripeAdapter _config) _since = do
    -- Webhook ベースのため、ポーリングは不要
    -- 代わりに handleWebhook を使用
    pure { processed: 0, errors: [], events: [] }

--------------------------------------------------------------------------------
-- ヘルパー
--------------------------------------------------------------------------------

foreign import getCurrentTime :: Aff Number
foreign import parseFloat :: String -> Number
foreign import floor :: Number -> Number
foreign import abs :: Number -> Number
foreign import take :: Int -> String -> String
foreign import drop :: Int -> String -> String
foreign import any :: forall a. (a -> Boolean) -> Array a -> Boolean
