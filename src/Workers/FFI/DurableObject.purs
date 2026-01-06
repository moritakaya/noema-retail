-- | Cloudflare Workers Durable Objects FFI
-- |
-- | Durable Objects へのバインディング。
-- |
-- | 圏論的解釈：
-- | Durable Object は A-algebra として機能する。
-- | - 状態を presheaf G として保持
-- | - Intent（arrow term）を受け取り、状態を更新
module Workers.FFI.DurableObject
  ( DurableObjectState
  , DurableObjectId
  , DurableObjectStub
  , DurableObjectNamespace
  , DurableObjectStorage
  , Env
  -- State
  , getStorage
  , getId
  , waitUntil
  -- Namespace
  , idFromName
  , idFromString
  , newUniqueId
  , get
  -- Stub
  , fetch
  -- Storage
  , storageGet
  , storagePut
  , storageDelete
  , storageList
  , storageTransaction
  , setAlarm
  , getAlarm
  , deleteAlarm
  -- SQL Storage
  , getSql
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Foreign (Foreign)
import Workers.FFI.Request (Request)
import Workers.FFI.Response (Response)
import Workers.FFI.SqlStorage (SqlStorage)

-- | Durable Object State
foreign import data DurableObjectState :: Type

-- | Durable Object ID
foreign import data DurableObjectId :: Type

-- | Durable Object Stub（プロキシ）
foreign import data DurableObjectStub :: Type

-- | Durable Object Namespace
foreign import data DurableObjectNamespace :: Type

-- | Durable Object Storage
foreign import data DurableObjectStorage :: Type

-- | Worker Environment
foreign import data Env :: Type

--------------------------------------------------------------------------------
-- State 操作
--------------------------------------------------------------------------------

-- | Storage を取得
foreign import getStorage :: DurableObjectState -> DurableObjectStorage

-- | ID を取得
foreign import _getId :: DurableObjectState -> DurableObjectId

getId :: DurableObjectState -> DurableObjectId
getId = _getId

-- | waitUntil（バックグラウンドタスク）
foreign import _waitUntil :: DurableObjectState -> Effect Unit -> Effect Unit

waitUntil :: DurableObjectState -> Effect Unit -> Effect Unit
waitUntil = _waitUntil

--------------------------------------------------------------------------------
-- Namespace 操作
--------------------------------------------------------------------------------

-- | 名前から ID を生成
foreign import _idFromName :: DurableObjectNamespace -> String -> Effect DurableObjectId

idFromName :: DurableObjectNamespace -> String -> Effect DurableObjectId
idFromName = _idFromName

-- | 文字列から ID を生成
foreign import _idFromString :: DurableObjectNamespace -> String -> Effect (Nullable DurableObjectId)

idFromString :: DurableObjectNamespace -> String -> Effect (Maybe DurableObjectId)
idFromString ns str = toMaybe <$> _idFromString ns str

-- | ユニークな ID を生成
foreign import _newUniqueId :: DurableObjectNamespace -> Effect DurableObjectId

newUniqueId :: DurableObjectNamespace -> Effect DurableObjectId
newUniqueId = _newUniqueId

-- | ID から Stub を取得
foreign import _get :: DurableObjectNamespace -> DurableObjectId -> Effect DurableObjectStub

get :: DurableObjectNamespace -> DurableObjectId -> Effect DurableObjectStub
get = _get

--------------------------------------------------------------------------------
-- Stub 操作
--------------------------------------------------------------------------------

-- | Stub を通じてリクエストを送信
foreign import _fetch :: DurableObjectStub -> Request -> EffectFnAff Response

fetch :: DurableObjectStub -> Request -> Aff Response
fetch stub req = fromEffectFnAff $ _fetch stub req

--------------------------------------------------------------------------------
-- Storage 操作（Key-Value）
--------------------------------------------------------------------------------

-- | 値を取得
foreign import _storageGet :: DurableObjectStorage -> String -> EffectFnAff (Nullable Foreign)

storageGet :: DurableObjectStorage -> String -> Aff (Maybe Foreign)
storageGet storage key = toMaybe <$> fromEffectFnAff (_storageGet storage key)

-- | 値を保存
foreign import _storagePut :: DurableObjectStorage -> String -> Foreign -> EffectFnAff Unit

storagePut :: DurableObjectStorage -> String -> Foreign -> Aff Unit
storagePut storage key value = fromEffectFnAff $ _storagePut storage key value

-- | 値を削除
foreign import _storageDelete :: DurableObjectStorage -> String -> EffectFnAff Boolean

storageDelete :: DurableObjectStorage -> String -> Aff Boolean
storageDelete storage key = fromEffectFnAff $ _storageDelete storage key

-- | キーの一覧を取得
foreign import _storageList :: DurableObjectStorage -> EffectFnAff (Array String)

storageList :: DurableObjectStorage -> Aff (Array String)
storageList storage = fromEffectFnAff $ _storageList storage

-- | トランザクション実行
foreign import _storageTransaction :: forall a. DurableObjectStorage -> (DurableObjectStorage -> EffectFnAff a) -> EffectFnAff a

storageTransaction :: forall a. DurableObjectStorage -> (DurableObjectStorage -> Aff a) -> Aff a
storageTransaction storage action = fromEffectFnAff $ _storageTransaction storage \s ->
  -- Note: ここでは Aff を直接渡すことができないため、ネイティブ Promise 変換が必要
  -- 実際の実装では JS 側で処理する
  _storageTransaction storage (\_ -> _dummyAff)
  where
    _dummyAff :: EffectFnAff a
    _dummyAff = _storageTransaction storage (\_ -> _dummyAff)

--------------------------------------------------------------------------------
-- Alarm 操作
--------------------------------------------------------------------------------

-- | アラームを設定（Unix ミリ秒）
foreign import _setAlarm :: DurableObjectStorage -> Number -> EffectFnAff Unit

setAlarm :: DurableObjectStorage -> Number -> Aff Unit
setAlarm storage time = fromEffectFnAff $ _setAlarm storage time

-- | 現在のアラームを取得
foreign import _getAlarm :: DurableObjectStorage -> EffectFnAff (Nullable Number)

getAlarm :: DurableObjectStorage -> Aff (Maybe Number)
getAlarm storage = toMaybe <$> fromEffectFnAff (_getAlarm storage)

-- | アラームを削除
foreign import _deleteAlarm :: DurableObjectStorage -> EffectFnAff Unit

deleteAlarm :: DurableObjectStorage -> Aff Unit
deleteAlarm storage = fromEffectFnAff $ _deleteAlarm storage

--------------------------------------------------------------------------------
-- SQL Storage
--------------------------------------------------------------------------------

-- | SQL Storage を取得
foreign import getSql :: DurableObjectStorage -> SqlStorage
