-- | Noema Cognition: StorageInterpretation
-- |
-- | StorageF（ストレージ操作語彙）を Factum（事実）へ解釈する。
-- |
-- | ## 技術的語彙からの移行
-- |
-- | 旧名称「StorageHandler」から「StorageInterpretation」へ変更。
-- |
-- | 理由:
-- | 1. 技術は進歩し変化するが、哲学・意味論は安定している
-- | 2. Noema の語彙体系と整合（Interpretation = 解釈）
-- | 3. 「意味→意味」の直接的対話を実現
-- |
-- | ## 圏論的解釈
-- |
-- | Interpretation は A-algebra homomorphism として機能する。
-- | StorageF の操作を具体的な SQLite 呼び出しに変換し、
-- | 結果を Factum に持ち上げる。
-- |
-- | > 実行とは忘却である。
module Noema.Cognition.StorageInterpretation
  ( realizeStorageIntent
  , StorageEnv
  , SqlStorage
  , mkStorageEnv
  , interpretStorageF
  ) where

import Prelude

import Data.Maybe (Maybe)
import Foreign (Foreign)

import Noema.Vorzeichnung.Vocabulary.StorageF (StorageF(..), StorageIntent)
import Noema.Cognition.Interpretation (Interpretation, realizeInterpretation)
import Noema.Sedimentation.Factum (Factum)

-- ============================================================
-- 環境
-- ============================================================

-- | Storage 環境
-- |
-- | Interpretation の実行に必要な依存関係を保持する。
type StorageEnv =
  { sql :: SqlStorage
  }

-- | Storage 環境を作成
mkStorageEnv :: SqlStorage -> StorageEnv
mkStorageEnv sql = { sql }

-- | SQLite Storage の型（FFI から提供される）
foreign import data SqlStorage :: Type

-- ============================================================
-- Interpretation 実装
-- ============================================================

-- | StorageF を Factum に解釈する Interpretation
-- |
-- | 圏論的解釈:
-- | この関数は自然変換 StorageF ~> Factum を定義する。
-- | A-algebra homomorphism として、操作の構造を保存しながら
-- | 具体的な SQLite 実装へ変換する。
interpretStorageF :: StorageEnv -> Interpretation StorageF
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
-- Intent の実現（Realization）
-- ============================================================

-- | StorageIntent を実現する
-- |
-- | ## 哲学的基盤
-- |
-- | Husserl の「充実化」(Erfüllung):
-- | - 空虚な意志（Intent）が充実した事実（Factum）へと移行する過程
-- | - 「実行とは忘却である」：構造は消え、事実のみが残る
-- |
-- | 使用例:
-- | ```purescript
-- | result <- realizeStorageIntent env (querySql "SELECT * FROM users") unit
-- | -- result :: Factum (Array Foreign)
-- |
-- | -- エントリーポイントで Factum → Effect に変換
-- | handleRequest req = collapse do
-- |   result <- realizeStorageIntent env intent unit
-- |   ...
-- | ```
realizeStorageIntent :: forall a b. StorageEnv -> StorageIntent a b -> a -> Factum b
realizeStorageIntent env intent input =
  realizeInterpretation (interpretStorageF env) intent input

-- ============================================================
-- FFI 関数
-- ============================================================

foreign import exec :: SqlStorage -> String -> Cursor
foreign import execWithParams :: SqlStorage -> String -> Array Foreign -> Cursor
foreign import one :: Cursor -> Maybe Foreign
foreign import toArray :: Cursor -> Array Foreign

foreign import data Cursor :: Type
