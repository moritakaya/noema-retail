-- | Cloudflare Workers Response FFI
-- |
-- | Web API Response オブジェクトへのバインディング。
module Workers.FFI.Response
  ( Response
  , ResponseInit
  , status
  , statusText
  , ok
  , headers
  , text
  , json
  , newResponse
  , newResponseWithInit
  , jsonResponse
  , errorResponse
  , notFoundResponse
  , redirectResponse
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Foreign (Foreign)
import Foreign.Object (Object)
import Foreign.Object as Object

-- | Web API Response
foreign import data Response :: Type

-- | Response 初期化オプション
type ResponseInit =
  { status :: Int
  , statusText :: String
  , headers :: Object String
  }

-- | Response ステータスコード
foreign import status :: Response -> Int

-- | Response ステータステキスト
foreign import statusText :: Response -> String

-- | Response が成功か (2xx)
foreign import ok :: Response -> Boolean

-- | Response ヘッダー
foreign import _headers :: Response -> Effect (Object String)

headers :: Response -> Effect (Object String)
headers = _headers

-- | Response ボディをテキストとして取得
foreign import _text :: Response -> EffectFnAff String

text :: Response -> Aff String
text res = fromEffectFnAff $ _text res

-- | Response ボディを JSON として取得
foreign import _json :: Response -> EffectFnAff Foreign

json :: Response -> Aff Foreign
json res = fromEffectFnAff $ _json res

-- | 新しい Response を作成
foreign import _newResponse :: String -> Effect Response

newResponse :: String -> Effect Response
newResponse = _newResponse

-- | 初期化オプション付きで新しい Response を作成
foreign import _newResponseWithInit :: String -> ResponseInit -> Effect Response

newResponseWithInit :: String -> ResponseInit -> Effect Response
newResponseWithInit = _newResponseWithInit

-- | JSON Response を作成
jsonResponse :: forall a. a -> Effect Response
jsonResponse = _jsonResponse

foreign import _jsonResponse :: forall a. a -> Effect Response

-- | エラー Response を作成
errorResponse :: Int -> String -> Effect Response
errorResponse statusCode message = newResponseWithInit
  ("{\"error\":\"" <> message <> "\"}")
  { status: statusCode
  , statusText: "Error"
  , headers: Object.singleton "Content-Type" "application/json"
  }

-- | 404 Not Found Response
notFoundResponse :: String -> Effect Response
notFoundResponse = errorResponse 404

-- | リダイレクト Response
foreign import _redirectResponse :: String -> Int -> Effect Response

redirectResponse :: String -> Effect Response
redirectResponse location = _redirectResponse location 302
