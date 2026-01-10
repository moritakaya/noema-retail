-- | Noema Workers: Router
-- |
-- | HTTP ルーティング。
-- |
-- | ## Situierung 統合
-- |
-- | PartitionKey に基づく Attractor（DO）ルーティングをサポート。
-- | Situable 型クラスにより、語彙からルーティング先を静的に決定。
-- |
-- | ```purescript
-- | -- InventoryF 操作から PartitionKey を導出
-- | let key = situate (GetStock tid sid identity)
-- |     attractorId = resolveAttractor SubjectAttractorBinding key
-- | ```
module Platform.Cloudflare.Router
  ( -- * HTTP ルーティング
    Route(..)
  , RouteHandler
  , router
  , matchRoute
    -- * Situierung ルーティング
  , AttractorBinding(..)
  , resolveAttractor
  , resolveAttractors
  ) where

import Prelude

import Data.Array (filter, zipWith, all, uncons)
import Data.Maybe (Maybe(..))
import Data.String (split, Pattern(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Foreign.Object (Object)
import Foreign.Object as Object
import Platform.Cloudflare.FFI.Request (Request, url, method)
import Platform.Cloudflare.FFI.Response (Response)
import Noema.Vorzeichnung.Situierung
  ( PartitionKey(..)
  , PartitionScheme
  , applyScheme
  , partitionKeyComponents
  )

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
    go arr = case uncons arr of
      Nothing -> Nothing
      Just { head: r, tail: rs } -> case matchRoute r.route req of
        Just params -> Just $ r.handler params req
        Nothing -> go rs

--------------------------------------------------------------------------------
-- FFI ヘルパー
--------------------------------------------------------------------------------

foreign import parseUrlPath :: String -> Array String
foreign import startsWith :: String -> String -> Boolean
foreign import drop :: Int -> String -> String
foreign import length :: forall a. Array a -> Int

--------------------------------------------------------------------------------
-- Situierung ルーティング
--------------------------------------------------------------------------------

-- | Attractor（DO）へのバインディング
-- |
-- | Cloudflare Workers の環境バインディングに対応。
-- | 各 AttractorBinding は wrangler.json で定義された DO クラスを表す。
-- |
-- | ## 例
-- |
-- | ```toml
-- | # wrangler.json
-- | [durable_objects]
-- | bindings = [
-- |   { name = "SUBJECT_ATTRACTOR", class_name = "SubjectAttractor" },
-- |   { name = "CONTRACT_ATTRACTOR", class_name = "ContractAttractor" }
-- | ]
-- | ```
data AttractorBinding
  = SubjectAttractorBinding
    -- ^ Subject（主体）を管理する Attractor
  | ContractAttractorBinding
    -- ^ Contract（契約）を管理する Attractor
  | InventoryAttractorBinding
    -- ^ Inventory（在庫）を管理する Attractor（レガシー）

derive instance eqAttractorBinding :: Eq AttractorBinding

instance showAttractorBinding :: Show AttractorBinding where
  show SubjectAttractorBinding = "SUBJECT_ATTRACTOR"
  show ContractAttractorBinding = "CONTRACT_ATTRACTOR"
  show InventoryAttractorBinding = "INVENTORY_ATTRACTOR"

-- | PartitionKey を Attractor ID に変換
-- |
-- | PartitionKey と PartitionScheme に基づいて、
-- | 適切な Attractor の ID 文字列を生成する。
-- |
-- | ## ルーティングロジック
-- |
-- | - BySubject: SubjectAttractor へルーティング
-- | - ByThing: Thing を包摂する Subject の SubjectAttractor へ
-- | - ByContract: ContractAttractor へルーティング
-- | - ByHash: スキームに従ってパーティション
-- | - Composite: 最初のキーを使用（scatter-gather は resolveAttractors を使用）
-- | - Broadcast: 全 Attractor（呼び出し元で処理）
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | import Noema.Vorzeichnung.Situierung (class Situable, situate)
-- |
-- | routeInventoryOp :: InventoryF a -> String
-- | routeInventoryOp op =
-- |   let key = situate op
-- |   in resolveAttractor SubjectAttractorBinding Direct key
-- | ```
resolveAttractor :: AttractorBinding -> PartitionScheme -> PartitionKey -> String
resolveAttractor binding scheme key = case key of
  BySubject sid ->
    -- Subject 操作は SubjectAttractor へ
    applyScheme scheme (BySubject sid)

  ByThing _tid sid ->
    -- Thing 操作は包摂する Subject の Attractor へ
    applyScheme scheme (BySubject sid)

  ByContract cid ->
    -- Contract 操作は ContractAttractor へ
    applyScheme scheme (ByContract cid)

  ByHash h ->
    applyScheme scheme (ByHash h)

  Composite keys ->
    -- Composite の場合は最初のキーを使用
    case uncons keys of
      Just { head } -> resolveAttractor binding scheme head
      Nothing -> "broadcast:empty"

  Broadcast ->
    "broadcast:all"

-- | 複数の Attractor ID を解決（scatter-gather パターン用）
-- |
-- | Composite PartitionKey の各要素に対して Attractor ID を生成。
-- | 並列リクエスト時に使用。
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | -- 複数 Subject への分散操作
-- | let keys = Composite [BySubject sid1, BySubject sid2, BySubject sid3]
-- |     attractorIds = resolveAttractors SubjectAttractorBinding Direct keys
-- | -- attractorIds = ["subject:sid1", "subject:sid2", "subject:sid3"]
-- | ```
resolveAttractors :: AttractorBinding -> PartitionScheme -> PartitionKey -> Array String
resolveAttractors binding scheme key =
  map (resolveAttractor binding scheme) (partitionKeyComponents key)
