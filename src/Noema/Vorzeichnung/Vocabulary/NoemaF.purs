-- | Noema Vocabulary: NoemaF（統合語彙）
-- |
-- | 全ての語彙を統合した余積型。
-- | Noema の「意志のアルファベット」を構成する。
-- |
-- | ## 圏論的構造
-- |
-- | NoemaF = SubjectF + ThingF + RelationF + ContractF
-- |
-- | 単項関手の余積として定義。
-- | 各語彙は Base 圏、Fiber 圏、Span 圏、規定の圏に対応。
module Noema.Vorzeichnung.Vocabulary.NoemaF
  ( NoemaF
  , NoemaIntent
  -- Injection
  , inSubject
  , inThing
  , inRelation
  , inContract
  -- Intent lifting
  , liftSubject
  , liftThing
  , liftRelation
  , liftContract
  ) where

import Prelude

import Data.Functor.Coproduct (Coproduct, left, right)

import Noema.Vorzeichnung.Intent (Intent, hoistIntent)
import Noema.Vorzeichnung.Vocabulary.SubjectF (SubjectF)
import Noema.Vorzeichnung.Vocabulary.ThingF (ThingF)
import Noema.Vorzeichnung.Vocabulary.RelationF (RelationF)
import Noema.Vorzeichnung.Vocabulary.ContractF (ContractF)

-- ============================================================
-- NoemaF: 語彙の余積
-- ============================================================

-- | 語彙の余積 = Noema の「意志のアルファベット」
-- |
-- | 圏論的には:
-- | NoemaF i o = SubjectF i o + ThingF i o + RelationF i o + ContractF i o
-- |
-- | Coproduct の入れ子で表現:
-- | NoemaF = Coproduct SubjectF (Coproduct ThingF (Coproduct RelationF ContractF))
type NoemaF i = Coproduct (SubjectF i) (Coproduct (ThingF i) (Coproduct (RelationF i) (ContractF i)))

-- ============================================================
-- Intent 型
-- ============================================================

-- | Noema Intent の型
type NoemaIntent a b = Intent (NoemaF a) a b

-- ============================================================
-- Injection 関数
-- ============================================================

-- | SubjectF を NoemaF に injection
inSubject :: forall i. SubjectF i ~> NoemaF i
inSubject = left

-- | ThingF を NoemaF に injection
inThing :: forall i. ThingF i ~> NoemaF i
inThing = right <<< left

-- | RelationF を NoemaF に injection
inRelation :: forall i. RelationF i ~> NoemaF i
inRelation = right <<< right <<< left

-- | ContractF を NoemaF に injection
inContract :: forall i. ContractF i ~> NoemaF i
inContract = right <<< right <<< right

-- ============================================================
-- Intent lifting
-- ============================================================

-- | Subject Intent を Noema Intent に持ち上げ
liftSubject :: forall a b. Intent (SubjectF a) a b -> NoemaIntent a b
liftSubject = hoistIntent inSubject

-- | Thing Intent を Noema Intent に持ち上げ
liftThing :: forall a b. Intent (ThingF a) a b -> NoemaIntent a b
liftThing = hoistIntent inThing

-- | Relation Intent を Noema Intent に持ち上げ
liftRelation :: forall a b. Intent (RelationF a) a b -> NoemaIntent a b
liftRelation = hoistIntent inRelation

-- | Contract Intent を Noema Intent に持ち上げ
liftContract :: forall a b. Intent (ContractF a) a b -> NoemaIntent a b
liftContract = hoistIntent inContract

-- ============================================================
-- Handler の構成
-- ============================================================

-- | NoemaF の Handler は各コンポーネントの Handler の組み合わせ:
-- |
-- | ```purescript
-- | noemaHandler :: NoemaF ~> Effect
-- | noemaHandler = coproduct subjectHandler
-- |              $ coproduct thingHandler
-- |              $ coproduct relationHandler contractHandler
-- | ```
-- |
-- | これは余積の普遍性により導かれる:
-- | [h1, h2, h3, h4] : F1 + F2 + F3 + F4 → G
-- | where h1 : F1 → G, h2 : F2 → G, h3 : F3 → G, h4 : F4 → G
