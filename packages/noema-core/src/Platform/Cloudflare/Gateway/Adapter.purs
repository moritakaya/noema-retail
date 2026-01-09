-- | Platform.Cloudflare.Gateway.Adapter
-- |
-- | 汎用 Gateway アダプターの基底型クラス。
-- | Inventory 等のドメイン固有機能に依存しない。
-- |
-- | 圏論的解釈：
-- | Gateway は Platform（台）から外界への射として機能する。
-- | Adapter は外部システムとの通信プロトコルを抽象化する。
module Platform.Cloudflare.Gateway.Adapter
  ( class GatewayAdapter
  , adapterName
  , healthCheck
  -- Types
  , AdapterConfig
  , AdapterError(..)
  -- Utilities
  , handleAdapterError
  , retryWithBackoff
  , isRetryable
  ) where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff, delay)
import Effect.Aff.Class (class MonadAff, liftAff)
import Data.Time.Duration (Milliseconds(..))

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

-- | 汎用 Gateway アダプター型クラス
-- |
-- | 各外部システムとの接続はこのインターフェースを実装する。
-- | ドメイン固有のメソッド（getStock 等）は派生型クラスで定義。
class GatewayAdapter a where
  -- | アダプター名（識別用）
  adapterName :: a -> String

  -- | ヘルスチェック
  healthCheck :: a -> Aff (Either AdapterError Unit)

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
    toNumber = intToNumber

foreign import intToNumber :: Int -> Number

-- | レスポンスがリトライ可能か判定
isRetryable :: AdapterError -> Boolean
isRetryable = case _ of
  NetworkError _ -> true
  RateLimitError _ -> true
  ApiError status _ | status >= 500 -> true
  _ -> false
