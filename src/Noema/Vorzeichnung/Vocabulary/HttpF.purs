-- | Noema Effect: HttpF
-- |
-- | HTTP 操作を表す Functor。
-- | 外部 API との通信を抽象化する。
module Noema.Vorzeichnung.Vocabulary.HttpF
  ( HttpF(..)
  , HttpIntent
  , HttpError(..)
  , HttpResponse
  -- Smart constructors
  , httpGet
  , httpPost
  , httpPut
  , httpDelete
  , httpGetJson
  , httpPostJson
  ) where

import Prelude

import Data.Either (Either)
import Data.Maybe (Maybe)
import Foreign (Foreign)
import Foreign.Object (Object)
import Noema.Vorzeichnung.Freer (Intent, liftIntent)

-- | HTTP レスポンス
type HttpResponse =
  { status :: Int
  , statusText :: String
  , headers :: Object String
  , body :: String
  }

-- | HTTP エラー
data HttpError
  = NetworkError String
  | HttpStatusError Int String
  | ParseError String
  | TimeoutError

derive instance Eq HttpError
instance Show HttpError where
  show = case _ of
    NetworkError msg -> "NetworkError: " <> msg
    HttpStatusError status msg -> "HttpStatusError(" <> show status <> "): " <> msg
    ParseError msg -> "ParseError: " <> msg
    TimeoutError -> "TimeoutError"

-- | HTTP 操作の Functor
data HttpF next
  = HttpGet String (Object String) (Either HttpError HttpResponse -> next)
  | HttpPost String (Object String) String (Either HttpError HttpResponse -> next)
  | HttpPut String (Object String) String (Either HttpError HttpResponse -> next)
  | HttpDelete String (Object String) (Either HttpError HttpResponse -> next)
  | HttpPatch String (Object String) String (Either HttpError HttpResponse -> next)

derive instance Functor HttpF

-- | HTTP 操作の Intent
type HttpIntent = Intent HttpF

--------------------------------------------------------------------------------
-- Smart Constructors
--------------------------------------------------------------------------------

-- | GET リクエスト
httpGet :: String -> Object String -> HttpIntent (Either HttpError HttpResponse)
httpGet url headers = liftIntent $ HttpGet url headers identity

-- | POST リクエスト
httpPost :: String -> Object String -> String -> HttpIntent (Either HttpError HttpResponse)
httpPost url headers body = liftIntent $ HttpPost url headers body identity

-- | PUT リクエスト
httpPut :: String -> Object String -> String -> HttpIntent (Either HttpError HttpResponse)
httpPut url headers body = liftIntent $ HttpPut url headers body identity

-- | DELETE リクエスト
httpDelete :: String -> Object String -> HttpIntent (Either HttpError HttpResponse)
httpDelete url headers = liftIntent $ HttpDelete url headers identity

-- | GET リクエスト（JSON パース）
httpGetJson :: String -> Object String -> HttpIntent (Either HttpError Foreign)
httpGetJson url headers = do
  response <- httpGet url headers
  pure $ response >>= parseJson
  where
    parseJson :: HttpResponse -> Either HttpError Foreign
    parseJson resp =
      -- TODO: 実際の JSON パース
      pure $ unsafeToForeign resp.body

-- | POST リクエスト（JSON）
httpPostJson :: String -> Object String -> Foreign -> HttpIntent (Either HttpError Foreign)
httpPostJson url headers body = do
  let jsonBody = stringifyJson body
  response <- httpPost url headers jsonBody
  pure $ response >>= parseJson
  where
    parseJson :: HttpResponse -> Either HttpError Foreign
    parseJson resp = pure $ unsafeToForeign resp.body

    stringifyJson :: Foreign -> String
    stringifyJson = unsafeStringify

foreign import unsafeToForeign :: forall a. a -> Foreign
foreign import unsafeStringify :: Foreign -> String
