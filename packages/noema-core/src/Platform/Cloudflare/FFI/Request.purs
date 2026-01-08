-- | Cloudflare Workers Request FFI
-- |
-- | Web API Request オブジェクトへのバインディング。
module Platform.Cloudflare.FFI.Request
  ( Request
  , RequestInit
  , Method(..)
  , url
  , method
  , headers
  , text
  , json
  , newRequest
  , newRequestWithInit
  , methodToString
  , clone
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Foreign (Foreign)
import Foreign.Object (Object)

-- | Web API Request
foreign import data Request :: Type

-- | HTTP メソッド
data Method
  = GET
  | POST
  | PUT
  | DELETE
  | PATCH
  | HEAD
  | OPTIONS

derive instance Eq Method

methodToString :: Method -> String
methodToString = case _ of
  GET -> "GET"
  POST -> "POST"
  PUT -> "PUT"
  DELETE -> "DELETE"
  PATCH -> "PATCH"
  HEAD -> "HEAD"
  OPTIONS -> "OPTIONS"

-- | Request 初期化オプション
type RequestInit =
  { method :: String
  , headers :: Object String
  , body :: Nullable String
  }

-- | Request URL を取得
foreign import url :: Request -> String

-- | Request メソッドを取得
foreign import _method :: Request -> String

method :: Request -> String
method = _method

-- | Request ヘッダーを取得
foreign import _getHeader :: Request -> String -> Effect (Nullable String)

getHeader :: Request -> String -> Effect (Maybe String)
getHeader req name = toMaybe <$> _getHeader req name

-- | すべてのヘッダーを取得
foreign import headers :: Request -> Effect (Object String)

-- | Request ボディをテキストとして取得
foreign import _text :: Request -> EffectFnAff String

text :: Request -> Aff String
text req = fromEffectFnAff $ _text req

-- | Request ボディを JSON として取得
foreign import _json :: Request -> EffectFnAff Foreign

json :: Request -> Aff Foreign
json req = fromEffectFnAff $ _json req

-- | 新しい Request を作成
foreign import _newRequest :: String -> Effect Request

newRequest :: String -> Effect Request
newRequest = _newRequest

-- | 初期化オプション付きで新しい Request を作成
foreign import _newRequestWithInit :: String -> RequestInit -> Effect Request

newRequestWithInit :: String -> RequestInit -> Effect Request
newRequestWithInit = _newRequestWithInit

-- | Request をクローン
foreign import clone :: Request -> Effect Request
