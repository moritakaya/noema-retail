-- | Cloudflare Workers Fetch FFI
-- |
-- | Web Fetch API へのバインディング。
-- | 外部 API との通信に使用する。
module Platform.Cloudflare.FFI.Fetch
  ( fetch
  , fetchWithInit
  , FetchInit
  , Method(..)
  , methodToString
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, toNullable)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Foreign.Object (Object)
import Platform.Cloudflare.FFI.Response (Response)

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

-- | Fetch 初期化オプション
type FetchInit =
  { method :: String
  , headers :: Object String
  , body :: Nullable String
  }

-- | URL を fetch
foreign import _fetch :: String -> EffectFnAff Response

fetch :: String -> Aff Response
fetch url = fromEffectFnAff $ _fetch url

-- | オプション付きで fetch
foreign import _fetchWithInit :: String -> FetchInit -> EffectFnAff Response

fetchWithInit :: String -> FetchInit -> Aff Response
fetchWithInit url init = fromEffectFnAff $ _fetchWithInit url init

-- | 便利な fetch 関数
fetchGet :: String -> Object String -> Aff Response
fetchGet url headers = fetchWithInit url
  { method: "GET"
  , headers
  , body: toNullable Nothing
  }

fetchPost :: String -> Object String -> String -> Aff Response
fetchPost url headers body = fetchWithInit url
  { method: "POST"
  , headers
  , body: toNullable (Just body)
  }

fetchPut :: String -> Object String -> String -> Aff Response
fetchPut url headers body = fetchWithInit url
  { method: "PUT"
  , headers
  , body: toNullable (Just body)
  }

fetchDelete :: String -> Object String -> Aff Response
fetchDelete url headers = fetchWithInit url
  { method: "DELETE"
  , headers
  , body: toNullable Nothing
  }
