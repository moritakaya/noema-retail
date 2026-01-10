-- | Noema Cognition: NoemaInterpretation
-- |
-- | NoemaF（統合語彙）を Factum（事実）へ解釈する。
-- |
-- | ## 役割
-- |
-- | 4つの語彙（SubjectF, ThingF, RelationF, ContractF）を統合した
-- | NoemaF に対する Interpretation を提供する。
-- |
-- | ## 圏論的解釈
-- |
-- | NoemaF = SubjectF + ThingF + RelationF + ContractF（余積）
-- |
-- | 余積の普遍性により、各コンポーネントの Interpretation から
-- | 全体の Interpretation が導かれる：
-- |
-- | [h1, h2, h3, h4] : F1 + F2 + F3 + F4 → Factum
-- | where h1 : F1 → Factum, h2 : F2 → Factum, ...
-- |
-- | ## 使用例
-- |
-- | ```purescript
-- | env <- recognize $ mkNoemaEnv sql
-- | result <- realizeNoemaIntent env (liftSubject (createSubject init)) unit
-- | -- result :: Factum SubjectId
-- | ```
module Noema.Cognition.NoemaInterpretation
  ( realizeNoemaIntent
  , NoemaEnv
  , NoemaIntent
  , mkNoemaEnv
  , initializeNoemaSchema
  , interpretNoemaF
  ) where

import Prelude

import Data.Functor.Coproduct (coproduct)
import Effect (Effect)

import Noema.Vorzeichnung.Vocabulary.NoemaF (NoemaF)
import Noema.Vorzeichnung.Intent (Intent)
import Noema.Cognition.Interpretation (Interpretation, realizeInterpretation)
import Noema.Sedimentation.Factum (Factum)
import Platform.Cloudflare.FFI.SqlStorage (SqlStorage)

-- 各 Interpretation をインポート
import Noema.Cognition.SubjectInterpretation as Subject
import Noema.Cognition.ThingInterpretation as Thing
import Noema.Cognition.RelationInterpretation as Relation
import Noema.Cognition.ContractInterpretation as Contract

-- ============================================================
-- 環境
-- ============================================================

-- | Noema Interpretation 統合環境
-- |
-- | 4つの語彙すべてに対する環境を保持する。
type NoemaEnv =
  { subject :: Subject.SubjectEnv
  , thing :: Thing.ThingEnv
  , relation :: Relation.RelationEnv
  , contract :: Contract.ContractEnv
  }

-- | 統合環境を作成
-- |
-- | 単一の SqlStorage から全ての環境を生成する。
-- | 同一の DO 内で全ての語彙を扱う場合に使用。
mkNoemaEnv :: SqlStorage -> NoemaEnv
mkNoemaEnv sql =
  { subject: Subject.mkSubjectEnv sql
  , thing: Thing.mkThingEnv sql
  , relation: Relation.mkRelationEnv sql
  , contract: Contract.mkContractEnv sql
  }

-- ============================================================
-- スキーマ初期化
-- ============================================================

-- | 全スキーマを初期化
-- |
-- | Durable Object の初回アクセス時に呼び出す。
-- | Subject, Thing, Relation, Contract の全スキーマを初期化する。
initializeNoemaSchema :: SqlStorage -> Effect Unit
initializeNoemaSchema sql = do
  Subject.initializeSubjectSchema sql
  Thing.initializeThingSchema sql
  Relation.initializeRelationSchema sql
  Contract.initializeContractSchema sql

-- ============================================================
-- Interpretation 実装
-- ============================================================

-- | NoemaF を Factum に解釈する Interpretation
-- |
-- | 圏論的解釈:
-- | 余積の普遍性により、各コンポーネントの Interpretation から導出。
-- |
-- | NoemaF = Coproduct SubjectF (Coproduct ThingF (Coproduct RelationF ContractF))
-- |
-- | interpretNoemaF = coproduct interpretSubjectF
-- |                 $ coproduct interpretThingF
-- |                 $ coproduct interpretRelationF interpretContractF
interpretNoemaF :: NoemaEnv -> Interpretation (NoemaF Unit)
interpretNoemaF env =
  coproduct (Subject.interpretSubjectF env.subject)
  $ coproduct (Thing.interpretThingF env.thing)
  $ coproduct (Relation.interpretRelationF env.relation)
               (Contract.interpretContractF env.contract)

-- ============================================================
-- Intent 実行
-- ============================================================

-- | NoemaIntent の型エイリアス
-- |
-- | 入力型が Unit に固定されている。
-- | 各語彙の Intent を liftSubject 等で持ち上げて使用する。
type NoemaIntent a b = Intent (NoemaF Unit) a b

-- | NoemaIntent を実現する
-- |
-- | ## 哲学的基盤
-- |
-- | Husserl の「充実化」(Erfüllung):
-- | - 空虚な意志（Intent）が充実した事実（Factum）へと移行する過程
-- | - 「実行とは忘却である」：構造は消え、事実のみが残る
-- |
-- | 4つの語彙すべてを統一的に扱える。
-- |
-- | 使用例:
-- | ```purescript
-- | -- Subject 操作
-- | subjectResult <- realizeNoemaIntent env (liftSubject (createSubject init)) unit
-- |
-- | -- Thing 操作
-- | thingResult <- realizeNoemaIntent env (liftThing (getProperty tid key)) unit
-- |
-- | -- Relation 操作
-- | relationResult <- realizeNoemaIntent env (liftRelation (addRelation init)) unit
-- |
-- | -- Contract 操作
-- | contractResult <- realizeNoemaIntent env (liftContract (proposeContract proposal)) unit
-- | ```
realizeNoemaIntent :: forall a b. NoemaEnv -> NoemaIntent a b -> a -> Factum b
realizeNoemaIntent env intent input =
  realizeInterpretation (interpretNoemaF env) intent input
