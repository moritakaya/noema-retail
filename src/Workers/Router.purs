-- | Noema Workers: Router
-- |
-- | HTTP ルーティング。
module Workers.Router
  ( Route(..)
  , RouteHandler
  , router
  , matchRoute
  ) where

import Prelude

import Data.Array (filter, zipWith, all)
import Data.Maybe (Maybe(..))
import Data.String (split, Pattern(..))
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Workers.FFI.Request (Request, url, method)

-- | ルート定義
data Route
  = GET String
  | POST String
  | PUT String
  | DELETE String
  | PATCH String

-- | ルートハンドラーの型
type RouteHandler params = params -> Request -> Effect Response

-- | ルートをマッチング
matchRoute :: Route -> Request -> Maybe (Object String)
matchRoute route req =
  let reqMethod = method req
      reqPath = parseUrlPath (url req)
  in case route of
    GET pattern | reqMethod == "GET" -> matchPattern pattern reqPath
    POST pattern | reqMethod == "POST" -> matchPattern pattern reqPath
    PUT pattern | reqMethod == "PUT" -> matchPattern pattern reqPath
    DELETE pattern | reqMethod == "DELETE" -> matchPattern pattern reqPath
    PATCH pattern | reqMethod == "PATCH" -> matchPattern pattern reqPath
    _ -> Nothing

-- | パターンマッチング
-- |
-- | パターン例: "/inventory/:productId/:locationId"
-- | パス例: "/inventory/ABC123/warehouse"
-- | 結果: { productId: "ABC123", locationId: "warehouse" }
matchPattern :: String -> Array String -> Maybe (Object String)
matchPattern pattern path =
  let patternParts = filter (_ /= "") $ split (Pattern "/") pattern
      pathParts = path
  in if length patternParts /= length pathParts
     then Nothing
     else extractParams patternParts pathParts

-- | パラメータを抽出
extractParams :: Array String -> Array String -> Maybe (Object String)
extractParams patterns paths =
  let pairs = zipWith matchPart patterns paths
  in if all isJust' pairs
     then Just $ Object.fromFoldable $ catMaybes pairs
     else Nothing
  where
    matchPart :: String -> String -> Maybe (Tuple String String)
    matchPart pat path
      | startsWith ":" pat = Just $ Tuple (drop 1 pat) path
      | pat == path = Nothing -- マッチするがパラメータなし
      | otherwise = Nothing -- マッチしない（エラー）

    isJust' :: Maybe (Tuple String String) -> Boolean
    isJust' (Just _) = true
    isJust' Nothing = true -- パラメータなしも OK

    catMaybes :: Array (Maybe (Tuple String String)) -> Array (Tuple String String)
    catMaybes = filter isJust' >>> map fromJust'
      where
        fromJust' (Just x) = x
        fromJust' Nothing = Tuple "" ""

-- | 簡易ルーター
router :: forall a. Array { route :: Route, handler :: Object String -> Request -> a } -> Request -> Maybe a
router routes req = go routes
  where
    go [] = Nothing
    go (r : rs) = case matchRoute r.route req of
      Just params -> Just $ r.handler params req
      Nothing -> go rs

--------------------------------------------------------------------------------
-- ヘルパー
--------------------------------------------------------------------------------

foreign import parseUrlPath :: String -> Array String
foreign import startsWith :: String -> String -> Boolean
foreign import drop :: Int -> String -> String
foreign import length :: forall a. Array a -> Int

-- Re-export for module compatibility
import Effect (Effect)
import Workers.FFI.Response (Response)
