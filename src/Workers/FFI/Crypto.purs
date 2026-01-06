-- | Cloudflare Workers Crypto FFI
-- |
-- | Web Crypto API へのバインディング。
-- | HMAC 署名、ハッシュ計算などに使用する。
module Workers.FFI.Crypto
  ( hmacSha256
  , sha256
  , randomUUID
  , randomBytes
  , base64Encode
  , base64Decode
  , hexEncode
  , secureCompare
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.ArrayBuffer.Types (ArrayBuffer)

-- | HMAC-SHA256 を計算
-- |
-- | message: 署名対象のメッセージ
-- | secret: 秘密鍵
-- | 戻り値: 16進数エンコードされた署名
foreign import _hmacSha256 :: String -> String -> EffectFnAff String

hmacSha256 :: String -> String -> Aff String
hmacSha256 message secret = fromEffectFnAff $ _hmacSha256 message secret

-- | SHA-256 ハッシュを計算
foreign import _sha256 :: String -> EffectFnAff String

sha256 :: String -> Aff String
sha256 message = fromEffectFnAff $ _sha256 message

-- | ランダムな UUID を生成
foreign import randomUUID :: Effect String

-- | ランダムなバイト列を生成
foreign import _randomBytes :: Int -> Effect String

randomBytes :: Int -> Effect String
randomBytes = _randomBytes

-- | Base64 エンコード
foreign import base64Encode :: String -> String

-- | Base64 デコード
foreign import base64Decode :: String -> String

-- | 16進数エンコード
foreign import hexEncode :: String -> String

-- | タイミング攻撃対策の安全な文字列比較
-- |
-- | 長さが異なる場合も一定時間で比較を完了する。
foreign import secureCompare :: String -> String -> Boolean
