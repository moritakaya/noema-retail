-- | Cloudflare Workers SQLite Storage FFI
-- |
-- | Durable Objects の SQLite Storage へのバインディング。
-- |
-- | 圏論的解釈：
-- | SQLite は Attractor（Durable Object）の永続化層を提供する。
-- | イベントソーシングのログは、Cognition（忘却）の痕跡として記録される。
module Workers.FFI.SqlStorage
  ( SqlStorage
  , SqlCursor
  , SqlRow
  , exec
  , execWithParams
  , one
  , toArray
  , raw
  , columnNames
  , rowsRead
  , rowsWritten
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Foreign (Foreign)

-- | SQLite Storage
foreign import data SqlStorage :: Type

-- | SQL Cursor（クエリ結果）
foreign import data SqlCursor :: Type

-- | SQL 行データ
type SqlRow = Foreign

--------------------------------------------------------------------------------
-- クエリ実行
--------------------------------------------------------------------------------

-- | SQL を実行（パラメータなし）
-- |
-- | 同期的に実行される点に注意。
-- | Cloudflare Workers の SQLite Storage はインメモリで高速。
foreign import exec :: SqlStorage -> String -> SqlCursor

-- | SQL を実行（パラメータあり）
-- |
-- | プレースホルダー ? を使用してパラメータを埋め込む。
-- | SQL インジェクション対策のため、ユーザー入力は必ずパラメータ化すること。
foreign import _execWithParams :: SqlStorage -> String -> Array Foreign -> SqlCursor

execWithParams :: SqlStorage -> String -> Array Foreign -> SqlCursor
execWithParams = _execWithParams

--------------------------------------------------------------------------------
-- 結果取得
--------------------------------------------------------------------------------

-- | 最初の1行を取得
foreign import _one :: SqlCursor -> Nullable SqlRow

one :: SqlCursor -> Maybe SqlRow
one cursor = toMaybe $ _one cursor

-- | すべての行を配列として取得
foreign import toArray :: SqlCursor -> Array SqlRow

-- | 生の結果を取得（配列の配列）
foreign import raw :: SqlCursor -> Array (Array Foreign)

--------------------------------------------------------------------------------
-- メタデータ
--------------------------------------------------------------------------------

-- | カラム名を取得
foreign import columnNames :: SqlCursor -> Array String

-- | 読み取った行数
foreign import rowsRead :: SqlCursor -> Int

-- | 書き込んだ行数
foreign import rowsWritten :: SqlCursor -> Int
