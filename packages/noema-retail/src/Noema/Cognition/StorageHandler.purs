-- | Noema Handler: StorageHandler（Arrow版）
-- |
-- | StorageF を SQLite Storage へ解釈する Handler。
-- |
-- | ## Arrow 移行での変更点
-- |
-- | - `foldIntent` → `runIntent`
-- | - Handler の型は変わらない（f ~> m）
-- | - Intent の実行時に入力値を渡す必要がある
-- |
-- | ## 圏論的解釈
-- |
-- | Handler は A-algebra homomorphism として機能する。
-- | StorageF の操作を具体的な SQLite 呼び出しに変換し、
-- | 結果を Effect に持ち上げる。
-- |
-- | > 実行とは忘却である。
module Noema.Cognition.StorageHandler
  ( runStorageIntent
  , StorageEnv
  , SqlStorage
  , mkStorageEnv
  , interpretStorageF
  ) where

import Prelude

import Data.Maybe (Maybe)
import Effect (Effect)
import Foreign (Foreign)

import Noema.Vorzeichnung.Vocabulary.StorageF (StorageF(..), StorageIntent)
import Noema.Vorzeichnung.Intent (runIntent)
import Noema.Cognition.Handler (Handler)

-- ============================================================
-- 環境
-- ============================================================

-- | Storage 環境
-- |
-- | Handler の実行に必要な依存関係を保持する。
type StorageEnv =
  { sql :: SqlStorage
  }

-- | Storage 環境を作成
mkStorageEnv :: SqlStorage -> StorageEnv
mkStorageEnv sql = { sql }

-- | SQLite Storage の型（FFI から提供される）
foreign import data SqlStorage :: Type

-- ============================================================
-- Handler 実装
-- ============================================================

-- | StorageF を Effect に解釈する Handler
-- |
-- | 圏論的解釈:
-- | この関数は自然変換 StorageF ~> Effect を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な SQLite 実装へ変換する。
interpretStorageF :: StorageEnv -> Handler StorageF Effect
interpretStorageF env = case _ of
  ExecSql sql next -> do
    let _ = exec env.sql sql
    pure next

  ExecSqlWithParams sql params next -> do
    let _ = execWithParams env.sql sql params
    pure next

  QuerySql sql k -> do
    let cursor = exec env.sql sql
        results = toArray cursor
    pure (k results)

  QuerySqlWithParams sql params k -> do
    let cursor = execWithParams env.sql sql params
        results = toArray cursor
    pure (k results)

  QueryOneSql sql k -> do
    let cursor = exec env.sql sql
        result = one cursor
    pure (k result)

  QueryOneSqlWithParams sql params k -> do
    let cursor = execWithParams env.sql sql params
        result = one cursor
    pure (k result)

  BeginTransaction next -> do
    let _ = exec env.sql "BEGIN TRANSACTION"
    pure next

  CommitTransaction next -> do
    let _ = exec env.sql "COMMIT"
    pure next

  RollbackTransaction next -> do
    let _ = exec env.sql "ROLLBACK"
    pure next

-- ============================================================
-- Intent 実行
-- ============================================================

-- | StorageIntent を Effect で実行する
-- |
-- | Arrow 版では入力値を明示的に渡す必要がある。
-- |
-- | ```purescript
-- | -- 使用例
-- | result <- runStorageIntent env (querySql "SELECT * FROM users") unit
-- | ```
runStorageIntent :: forall a b. StorageEnv -> StorageIntent a b -> a -> Effect b
runStorageIntent env intent input = 
  runIntent (interpretStorageF env) intent input

-- ============================================================
-- FFI 関数
-- ============================================================

foreign import exec :: SqlStorage -> String -> Cursor
foreign import execWithParams :: SqlStorage -> String -> Array Foreign -> Cursor
foreign import one :: Cursor -> Maybe Foreign
foreign import toArray :: Cursor -> Array Foreign

foreign import data Cursor :: Type
