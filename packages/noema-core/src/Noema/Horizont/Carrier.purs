-- | Noema Horizont: Carrier（担体）
-- |
-- | 外界との接続を担う基底型クラス。
-- | Horizont（地平線）は Intent が外界と接触する境界であり、
-- | Carrier はその境界を越えて外部データを「担う」構造である。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Horizont は外的前層 Channel^op → Set を表現する。
-- | Carrier は A-algebra の carrier（台集合）に対応し、
-- | 外部システムとの通信プロトコルを抽象化する。
-- |
-- | ## 現象学的基盤
-- |
-- | Horizont はフッサール現象学における「地平線」に由来する。
-- | 意識の対象を取り巻く潜在的経験の場であり、
-- | 今は主題的に捉えられていないが常に「そこにある」背景。
module Noema.Horizont.Carrier
  ( class Carrier
  , carrierName
  , healthCheck
  -- Types
  , CarrierConfig
  , CarrierError(..)
  -- Utilities
  , handleCarrierError
  , retryWithBackoff
  , isRetryable
  ) where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff, delay)
import Effect.Aff.Class (class MonadAff, liftAff)
import Data.Time.Duration (Milliseconds(..))

-- | Carrier 設定の共通型
type CarrierConfig =
  { apiBaseUrl :: String
  , timeout :: Int  -- ミリ秒
  }

-- | Carrier エラー
-- |
-- | 外界との接触で発生しうるエラーを表現する。
-- | 地平線（Horizont）を越える際の障害。
data CarrierError
  = AuthenticationError String
  | NetworkError String
  | RateLimitError Int  -- リトライまでの秒数
  | ApiError Int String  -- ステータスコード、メッセージ
  | ParseError String
  | ConfigurationError String

derive instance Eq CarrierError

instance Show CarrierError where
  show = case _ of
    AuthenticationError msg -> "AuthenticationError: " <> msg
    NetworkError msg -> "NetworkError: " <> msg
    RateLimitError seconds -> "RateLimitError: retry after " <> show seconds <> " seconds"
    ApiError status msg -> "ApiError(" <> show status <> "): " <> msg
    ParseError msg -> "ParseError: " <> msg
    ConfigurationError msg -> "ConfigurationError: " <> msg

-- | Carrier 型クラス
-- |
-- | 外界との接続を担う基底型クラス。
-- | 各外部システム（Channel）はこのインターフェースを実装する。
-- | ドメイン固有のメソッド（getStock 等）は派生型クラスで定義。
class Carrier a where
  -- | Carrier 名（識別用）
  carrierName :: a -> String

  -- | ヘルスチェック
  healthCheck :: a -> Aff (Either CarrierError Unit)

--------------------------------------------------------------------------------
-- ユーティリティ
--------------------------------------------------------------------------------

-- | エラーハンドリング
handleCarrierError :: forall a. CarrierError -> Aff (Either CarrierError a)
handleCarrierError err = pure $ Left err

-- | エクスポネンシャルバックオフでリトライ
-- |
-- | 地平線を越える際のネットワークエラーやレート制限に対して
-- | 指数バックオフでリトライする。
retryWithBackoff
  :: forall m a
   . MonadAff m
  => Int  -- 最大リトライ回数
  -> Int  -- 初期待機時間（ミリ秒）
  -> m (Either CarrierError a)
  -> m (Either CarrierError a)
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
isRetryable :: CarrierError -> Boolean
isRetryable = case _ of
  NetworkError _ -> true
  RateLimitError _ -> true
  ApiError status _ | status >= 500 -> true
  _ -> false
