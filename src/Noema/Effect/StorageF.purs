-- | Noema Effect: StorageF
-- |
-- | SQLite Storage 操作を表す Functor。
-- |
-- | 圏論的解釈：
-- | StorageF は永続化層への操作を抽象化する。
-- | Handler により具体的な SQLite 実装へ解釈される。
module Noema.Effect.StorageF
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
import Noema.Intent.Freer (Intent, liftIntent)

-- | SQLite Storage 操作の Functor
-- |
-- | Arrow Effects の制約に従い、操作は線形な列として設計。
-- | 条件分岐は許可されない。
data StorageF next
  -- DDL/DML（結果を返さない）
  = ExecSql String next
  | ExecSqlWithParams String (Array Foreign) next
  -- クエリ（複数行）
  | QuerySql String (Array Foreign -> next)
  | QuerySqlWithParams String (Array Foreign) (Array Foreign -> next)
  -- クエリ（単一行）
  | QueryOneSql String (Maybe Foreign -> next)
  | QueryOneSqlWithParams String (Array Foreign) (Maybe Foreign -> next)
  -- トランザクション制御
  | BeginTransaction next
  | CommitTransaction next
  | RollbackTransaction next

derive instance Functor StorageF

-- | Storage 操作の Intent
type StorageIntent = Intent StorageF

--------------------------------------------------------------------------------
-- Smart Constructors
--------------------------------------------------------------------------------

-- | SQL を実行（DDL/DML）
execSql :: String -> StorageIntent Unit
execSql sql = liftIntent $ ExecSql sql unit

-- | パラメータ付き SQL を実行
execSqlWithParams :: String -> Array Foreign -> StorageIntent Unit
execSqlWithParams sql params = liftIntent $ ExecSqlWithParams sql params unit

-- | SQL クエリを実行（複数行）
querySql :: String -> StorageIntent (Array Foreign)
querySql sql = liftIntent $ QuerySql sql identity

-- | パラメータ付き SQL クエリを実行（複数行）
querySqlWithParams :: String -> Array Foreign -> StorageIntent (Array Foreign)
querySqlWithParams sql params = liftIntent $ QuerySqlWithParams sql params identity

-- | SQL クエリを実行（単一行）
queryOneSql :: String -> StorageIntent (Maybe Foreign)
queryOneSql sql = liftIntent $ QueryOneSql sql identity

-- | パラメータ付き SQL クエリを実行（単一行）
queryOneSqlWithParams :: String -> Array Foreign -> StorageIntent (Maybe Foreign)
queryOneSqlWithParams sql params = liftIntent $ QueryOneSqlWithParams sql params identity

-- | トランザクション開始
beginTransaction :: StorageIntent Unit
beginTransaction = liftIntent $ BeginTransaction unit

-- | トランザクションコミット
commitTransaction :: StorageIntent Unit
commitTransaction = liftIntent $ CommitTransaction unit

-- | トランザクションロールバック
rollbackTransaction :: StorageIntent Unit
rollbackTransaction = liftIntent $ RollbackTransaction unit
