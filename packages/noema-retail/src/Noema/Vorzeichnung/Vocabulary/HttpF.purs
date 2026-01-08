-- | Noema Vocabulary: HttpF（単項関手版・Arrow対応）
-- |
-- | HTTP 操作を単項関手として定義。
-- | Arrow 制約（分岐禁止）は Intent レベルで強制される。
-- |
-- | 注意: do記法は使用できない。>>> 記法を使用する。
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
  , httpPatch
  ) where

import Prelude

import Data.Either (Either)
import Foreign.Object (Object)
import Noema.Vorzeichnung.Intent (Intent, liftEffect)

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

derive instance eqHttpError :: Eq HttpError

instance showHttpError :: Show HttpError where
  show = case _ of
    NetworkError msg -> "NetworkError: " <> msg
    HttpStatusError status msg -> "HttpStatusError(" <> show status <> "): " <> msg
    ParseError msg -> "ParseError: " <> msg
    TimeoutError -> "TimeoutError"

-- | HTTP 操作の Functor
-- |
-- | 継続渡しスタイル（CPS）で結果型を表現。
data HttpF a
  = HttpGet String (Object String) (Either HttpError HttpResponse -> a)
  | HttpPost String (Object String) String (Either HttpError HttpResponse -> a)
  | HttpPut String (Object String) String (Either HttpError HttpResponse -> a)
  | HttpDelete String (Object String) (Either HttpError HttpResponse -> a)
  | HttpPatch String (Object String) String (Either HttpError HttpResponse -> a)

derive instance functorHttpF :: Functor HttpF

-- | HTTP 操作の Intent
type HttpIntent a b = Intent HttpF a b

-- ============================================================
-- Smart Constructors
-- ============================================================

-- | GET リクエスト
-- |
-- | ```purescript
-- | httpGet "https://api.example.com/users" mempty
-- |   :: HttpIntent Unit (Either HttpError HttpResponse)
-- | ```
httpGet :: String -> Object String -> HttpIntent Unit (Either HttpError HttpResponse)
httpGet url headers = liftEffect (HttpGet url headers identity)

-- | POST リクエスト
-- |
-- | ```purescript
-- | httpPost "https://api.example.com/users" mempty "{\"name\":\"John\"}"
-- |   :: HttpIntent Unit (Either HttpError HttpResponse)
-- | ```
httpPost :: String -> Object String -> String -> HttpIntent Unit (Either HttpError HttpResponse)
httpPost url headers body = liftEffect (HttpPost url headers body identity)

-- | PUT リクエスト
httpPut :: String -> Object String -> String -> HttpIntent Unit (Either HttpError HttpResponse)
httpPut url headers body = liftEffect (HttpPut url headers body identity)

-- | DELETE リクエスト
httpDelete :: String -> Object String -> HttpIntent Unit (Either HttpError HttpResponse)
httpDelete url headers = liftEffect (HttpDelete url headers identity)

-- | PATCH リクエスト
httpPatch :: String -> Object String -> String -> HttpIntent Unit (Either HttpError HttpResponse)
httpPatch url headers body = liftEffect (HttpPatch url headers body identity)

-- ============================================================
-- Arrow 合成例（分岐なし）
-- ============================================================

-- | 以下は合法な Intent:
-- |
-- | ```purescript
-- | fetchAndProcess :: HttpIntent Unit String
-- | fetchAndProcess =
-- |   httpGet "https://api.example.com/data" mempty
-- |   >>> arrIntent (either (const "error") _.body)
-- | ```
-- |
-- | Either の処理は arrIntent 内で行う（分岐ではなく値の変換）

-- | 以下は違法（型エラー）:
-- |
-- | ```purescript
-- | illegalBranching =
-- |   httpGet url headers
-- |   >>> left (httpPost url2 headers2 body)  -- ArrowChoice がないので型エラー
-- | ```
