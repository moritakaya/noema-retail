-- | Noema Vocabulary: StorageF（単項関手版・Arrow対応）
-- |
-- | SQLite Storage 操作を単項関手として定義。
-- | Arrow 制約（分岐禁止）は Intent レベルで強制される。
-- |
-- | 設計原則:
-- | - Arrow Effects の制約に従い、操作は線形な列として設計
-- | - 条件分岐は禁止（Interpretation 層で処理）
-- | - do記法は使用できない。>>> 記法を使用する。
module Noema.Vorzeichnung.Vocabulary.StorageF
  ( StorageF(..)
  , StorageIntent
  -- Smart constructors
  , execSql
  , execSqlWithParams
  , querySql
  , querySqlWithParams
  , queryOneSql
  , queryOneSqlWithParams
  , beginTransaction
  , commitTransaction
  , rollbackTransaction
  ) where

import Prelude

import Data.Maybe (Maybe)
import Foreign (Foreign)
import Noema.Vorzeichnung.Intent (Intent, liftEffect)

-- | SQLite Storage 操作の Functor
-- |
-- | 継続渡しスタイル（CPS）で結果型を表現。
-- | Arrow Effects の制約に従い、操作は線形な列として設計。
data StorageF a
  -- DDL/DML（結果を返さない）
  = ExecSql String a
  | ExecSqlWithParams String (Array Foreign) a
  -- クエリ（複数行）
  | QuerySql String (Array Foreign -> a)
  | QuerySqlWithParams String (Array Foreign) (Array Foreign -> a)
  -- クエリ（単一行）
  | QueryOneSql String (Maybe Foreign -> a)
  | QueryOneSqlWithParams String (Array Foreign) (Maybe Foreign -> a)
  -- トランザクション制御
  | BeginTransaction a
  | CommitTransaction a
  | RollbackTransaction a

derive instance functorStorageF :: Functor StorageF

-- | Storage 操作の Intent
type StorageIntent a b = Intent StorageF a b

-- ============================================================
-- Smart Constructors
-- ============================================================

-- | SQL を実行（DDL/DML）
-- |
-- | ```purescript
-- | execSql "CREATE TABLE IF NOT EXISTS users (id TEXT PRIMARY KEY)"
-- |   :: StorageIntent Unit Unit
-- | ```
execSql :: String -> StorageIntent Unit Unit
execSql sql = liftEffect (ExecSql sql unit)

-- | パラメータ付き SQL を実行
-- |
-- | ```purescript
-- | execSqlWithParams "INSERT INTO users (id, name) VALUES (?, ?)" params
-- |   :: StorageIntent Unit Unit
-- | ```
execSqlWithParams :: String -> Array Foreign -> StorageIntent Unit Unit
execSqlWithParams sql params = liftEffect (ExecSqlWithParams sql params unit)

-- | SQL クエリを実行（複数行）
-- |
-- | ```purescript
-- | querySql "SELECT * FROM users"
-- |   :: StorageIntent Unit (Array Foreign)
-- | ```
querySql :: String -> StorageIntent Unit (Array Foreign)
querySql sql = liftEffect (QuerySql sql identity)

-- | パラメータ付き SQL クエリを実行（複数行）
querySqlWithParams :: String -> Array Foreign -> StorageIntent Unit (Array Foreign)
querySqlWithParams sql params = liftEffect (QuerySqlWithParams sql params identity)

-- | SQL クエリを実行（単一行）
-- |
-- | ```purescript
-- | queryOneSql "SELECT * FROM users WHERE id = 'user-1'"
-- |   :: StorageIntent Unit (Maybe Foreign)
-- | ```
queryOneSql :: String -> StorageIntent Unit (Maybe Foreign)
queryOneSql sql = liftEffect (QueryOneSql sql identity)

-- | パラメータ付き SQL クエリを実行（単一行）
queryOneSqlWithParams :: String -> Array Foreign -> StorageIntent Unit (Maybe Foreign)
queryOneSqlWithParams sql params = liftEffect (QueryOneSqlWithParams sql params identity)

-- | トランザクション開始
beginTransaction :: StorageIntent Unit Unit
beginTransaction = liftEffect (BeginTransaction unit)

-- | トランザクションコミット
commitTransaction :: StorageIntent Unit Unit
commitTransaction = liftEffect (CommitTransaction unit)

-- | トランザクションロールバック
rollbackTransaction :: StorageIntent Unit Unit
rollbackTransaction = liftEffect (RollbackTransaction unit)

-- ============================================================
-- Arrow 合成例（分岐なし）
-- ============================================================

-- | トランザクション内で複数操作
-- |
-- | ```purescript
-- | transactionalInsert :: Array Foreign -> StorageIntent Unit Unit
-- | transactionalInsert params =
-- |   beginTransaction
-- |   >>> execSqlWithParams "INSERT INTO users (id, name) VALUES (?, ?)" params
-- |   >>> commitTransaction
-- | ```
-- |
-- | 注意: エラー時のロールバックは Interpretation 層で処理する。
-- | Intent 層では線形な操作列のみを記述する。

-- | 以下は違法（ArrowChoice がないため型エラー）:
-- |
-- | ```purescript
-- | illegalBranching =
-- |   queryOneSql "SELECT * FROM users WHERE id = ?"
-- |   >>> arrIntent (\maybeUser -> case maybeUser of
-- |         Just _ -> Left ()
-- |         Nothing -> Right ())
-- |   >>> left (execSql "UPDATE ...")  -- 型エラー!
-- | ```
