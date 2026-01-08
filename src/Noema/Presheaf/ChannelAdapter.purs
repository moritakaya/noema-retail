-- | Noema Adapter: ChannelAdapter
-- |
-- | チャネルアダプターの基底型クラス。
-- | 各チャネル（楽天、Yahoo、スマレジ、Stripe）はこの型クラスを実装する。
-- |
-- | 圏論的解釈：
-- | ChannelAdapter は Functor の自然変換として機能する。
-- | チャネル固有の形式 → Noema 統一形式への変換を提供する。
module Noema.Presheaf.ChannelAdapter
  ( class ChannelAdapter
  , channel
  , getStock
  , setStock
  , syncToNoema
  , syncFromNoema
  , processOrders
  -- Types
  , AdapterConfig
  , AdapterError(..)
  , InventoryEvent(..)
  , StockInfo
  , OrderInfo
  -- Utilities
  , handleAdapterError
  , retryWithBackoff
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Effect.Aff (Aff, delay)
import Effect.Aff.Class (class MonadAff, liftAff)
import Data.Time.Duration (Milliseconds(..))
import Noema.Core.Locus (ThingId, Quantity, Timestamp)
import Noema.Presheaf.Channel (Channel)
import Noema.Vorzeichnung.Vocabulary.InventoryF (SyncResult(..))

-- | 在庫イベント型
-- |
-- | チャネルからの注文処理で生成されるイベント
data InventoryEvent
  = SaleEvent ThingId Quantity
  | ReturnEvent ThingId Quantity
  | AdjustEvent ThingId Quantity

-- | アダプター設定の共通型
type AdapterConfig =
  { apiBaseUrl :: String
  , timeout :: Int  -- ミリ秒
  }

-- | アダプターエラー
data AdapterError
  = AuthenticationError String
  | NetworkError String
  | RateLimitError Int  -- リトライまでの秒数
  | ApiError Int String  -- ステータスコード、メッセージ
  | ParseError String
  | ConfigurationError String

derive instance Eq AdapterError

instance Show AdapterError where
  show = case _ of
    AuthenticationError msg -> "AuthenticationError: " <> msg
    NetworkError msg -> "NetworkError: " <> msg
    RateLimitError seconds -> "RateLimitError: retry after " <> show seconds <> " seconds"
    ApiError status msg -> "ApiError(" <> show status <> "): " <> msg
    ParseError msg -> "ParseError: " <> msg
    ConfigurationError msg -> "ConfigurationError: " <> msg

-- | 在庫情報
type StockInfo =
  { productId :: String
  , quantity :: Int
  , lastUpdated :: Maybe Timestamp
  }

-- | 注文情報
type OrderInfo =
  { orderId :: String
  , items :: Array { productId :: String, quantity :: Int }
  , orderDate :: Timestamp
  , channel :: Channel
  }

-- | チャネルアダプター型クラス
-- |
-- | 各チャネルはこのインターフェースを実装する。
class ChannelAdapter a where
  -- | このアダプターが対応するチャネル
  channel :: a -> Channel

  -- | チャネルから在庫を取得
  getStock :: a -> ThingId -> Aff (Either AdapterError StockInfo)

  -- | チャネルの在庫を更新
  setStock :: a -> ThingId -> Quantity -> Aff (Either AdapterError Unit)

  -- | チャネル → Noema への同期
  syncToNoema :: a -> ThingId -> Aff SyncResult

  -- | Noema → チャネルへの同期
  syncFromNoema :: a -> ThingId -> Quantity -> Aff SyncResult

  -- | 新規注文を処理して在庫イベントを生成
  processOrders :: a -> Timestamp -> Aff { processed :: Int, errors :: Array String, events :: Array InventoryEvent }

--------------------------------------------------------------------------------
-- ユーティリティ
--------------------------------------------------------------------------------

-- | エラーハンドリング
handleAdapterError :: forall a. AdapterError -> Aff (Either AdapterError a)
handleAdapterError err = pure $ Left err

-- | エクスポネンシャルバックオフでリトライ
retryWithBackoff
  :: forall m a
   . MonadAff m
  => Int  -- 最大リトライ回数
  -> Int  -- 初期待機時間（ミリ秒）
  -> m (Either AdapterError a)
  -> m (Either AdapterError a)
retryWithBackoff maxRetries initialDelay action = go 0 initialDelay
  where
    go attempt currentDelay
      | attempt >= maxRetries = action
      | otherwise = do
          result <- action
          case result of
            Left (RateLimitError seconds) -> do
              liftAff $ delay (Milliseconds $ toNumber $ seconds * 1000)
              go (attempt + 1) currentDelay
            Left (NetworkError _) -> do
              liftAff $ delay (Milliseconds $ toNumber currentDelay)
              go (attempt + 1) (currentDelay * 2)
            other -> pure other

    toNumber :: Int -> Number
    toNumber = toNumber'

foreign import toNumber' :: Int -> Number

-- | レスポンスがリトライ可能か判定
isRetryable :: AdapterError -> Boolean
isRetryable = case _ of
  NetworkError _ -> true
  RateLimitError _ -> true
  ApiError status _ | status >= 500 -> true
  _ -> false
