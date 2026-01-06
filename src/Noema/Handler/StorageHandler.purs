-- | Noema Handler: StorageHandler
-- |
-- | StorageF を SQLite Storage へ解釈する Handler。
-- |
-- | 圏論的解釈：
-- | Handler は A-algebra homomorphism として機能する。
-- | StorageF の操作を具体的な SQLite 呼び出しに変換し、
-- | 結果を Effect/Aff に持ち上げる。
-- |
-- | > 実行とは忘却である。
-- | Handler による解釈は、Intent（意志構造）を忘却し、
-- | 事実（SQLite の状態変更）へと崩落させる。
module Noema.Handler.StorageHandler
  ( runStorageIntent
  , StorageEnv
  , mkStorageEnv
  ) where

import Prelude

import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Foreign (Foreign)
import Noema.Effect.StorageF (StorageF(..), StorageIntent)
import Noema.Intent.Freer (foldIntent)
import Workers.FFI.SqlStorage (SqlStorage, exec, execWithParams, one, toArray)

-- | Storage 環境
-- |
-- | Handler の実行に必要な依存関係を保持する。
type StorageEnv =
  { sql :: SqlStorage
  , inTransaction :: Boolean
  }

-- | Storage 環境を作成
mkStorageEnv :: SqlStorage -> StorageEnv
mkStorageEnv sql =
  { sql
  , inTransaction: false
  }

-- | StorageF を Effect に解釈する Handler
-- |
-- | 圏論的解釈：
-- | この関数は自然変換 StorageF ~> Effect を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な実装へ変換する。
interpretStorageF :: StorageEnv -> StorageF ~> Effect
interpretStorageF env = case _ of
  ExecSql sql next -> do
    let _ = exec env.sql sql
    pure next

  ExecSqlWithParams sql params next -> do
    let _ = execWithParams env.sql sql params
    pure next

  QuerySql sql cont -> do
    let cursor = exec env.sql sql
        results = toArray cursor
    pure $ cont results

  QuerySqlWithParams sql params cont -> do
    let cursor = execWithParams env.sql sql params
        results = toArray cursor
    pure $ cont results

  QueryOneSql sql cont -> do
    let cursor = exec env.sql sql
        result = one cursor
    pure $ cont result

  QueryOneSqlWithParams sql params cont -> do
    let cursor = execWithParams env.sql sql params
        result = one cursor
    pure $ cont result

  BeginTransaction next -> do
    let _ = exec env.sql "BEGIN TRANSACTION"
    pure next

  CommitTransaction next -> do
    let _ = exec env.sql "COMMIT"
    pure next

  RollbackTransaction next -> do
    let _ = exec env.sql "ROLLBACK"
    pure next

-- | StorageIntent を Effect で実行する
-- |
-- | 圏論的解釈：
-- | Cognition（認知による忘却）の具体化。
-- | Intent（Vorzeichnungsschema）を解釈し、
-- | SQLite の状態変更という事実へ崩落させる。
runStorageIntent :: StorageEnv -> StorageIntent ~> Effect
runStorageIntent env = foldIntent (interpretStorageF env)

-- | StorageIntent を Aff で実行する
-- |
-- | Effect を Aff に持ち上げるバージョン。
runStorageIntentAff :: forall m. MonadAff m => StorageEnv -> StorageIntent ~> m
runStorageIntentAff env intent = liftEffect $ runStorageIntent env intent
