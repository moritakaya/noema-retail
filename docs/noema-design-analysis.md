# Noema: 意味論と形式手法を統合する分散システムDSL

> 圏論的随伴構造を基盤とする DSL の設計評価と、人間・LLM 両方の認知に適合するアーキテクチャの考察

---

## TL;DR

- **設計に破綻なし**: Intent ⊣ Cognition 随伴は数学的に健全
- **革新点**: 「実行＝忘却」「法のバージョニング」「時間の三相（Husserl）」
- **形式手法統合**: PureScript → TLA+ → Test のフィードバックループ
- **LLM親和性**: 一貫した語彙（AVDC）と圏論的メタ言語

---

## 目次

1. [設計の客観的評価](#1-設計の客観的評価)
2. [既存設計手法との比較](#2-既存設計手法との比較)
3. [人間とLLMの認知構造](#3-人間とllmの認知構造)
4. [意味論の文脈](#4-意味論の文脈)
5. [形式手法の文脈](#5-形式手法の文脈)
6. [結論](#6-結論)

---

## 1. 設計の客観的評価

### 1.1 設計の強み

#### 随伴関手による責務分離

```
Intent ⊣ Cognition

Intent    : Prop → Struct  （自由関手：可能性の構造を生成）
Cognition : Struct → Prop  （忘却関手：構造を事実に崩落）
```

Clean Architecture や Hexagonal Architecture が「依存の方向」を制御するのに対し、Noema は「構造の生成と忘却」という圏論的操作で責務を分離する。これは単なるレイヤー分けではなく、数学的に well-defined な変換。

#### Arrow Effects による分岐禁止

```purescript
-- ArrowChoice を意図的に実装しない
class Arrow a where
  arr   :: (x -> y) -> a x y
  first :: a x y -> a (x,z) (y,z)
  -- left :: a x y -> a (Either x z) (Either y z)  -- 禁止
```

出力に基づく動的分岐を型レベルで禁止することで、Intent は常に「操作の列（sequence）」となる。これにより：

- TLA+ へのマッピングが自明になる
- モデル検査の状態空間が制限される
- 分岐は Handler（Cognition層）の責務として明確化

#### Vocabulary の余積構造

```purescript
type NoemaF i = Coproduct SubjectF
              (Coproduct ThingF
              (Coproduct RelationF ContractF))
```

4つの語彙（Subject, Thing, Relation, Contract）を余積で合成し、Handler も余積の普遍性で合成可能。DDD の Aggregate 境界を「余積の射影」として定式化している。

---

### 1.2 潜在的な設計課題

#### 課題1: Intent.purs と FreerArrow.purs の重複

| ファイル | 実装方式 | 状態 |
|----------|----------|------|
| Intent.purs | newtype + Exists | 本番使用 |
| FreerArrow.purs | data + unsafeCoerce | TODO/実験的 |

2つの類似実装が共存している。FreerArrow.purs は Profunctor ベースの異なるアプローチだが、TODO コメントと unsafeCoerce が残っている。

**推奨**: FreerArrow.purs を実験的（experimental）としてマークするか、Intent.purs に統合。

#### 課題2: Par における unsafeCoerce

```purescript
-- Intent.purs:131
first intent = unsafeCoerce (Intent (Par (mkExists (ParF { inner: intent }))))
```

存在型（Exists）による型隠蔽のため、並列合成で unsafeCoerce が必要。構築規律に依存した型安全性。

これは Freer Monad 実装の既知のトレードオフ。ランタイムでの型検査は不可能だが、スマートコンストラクタ経由でのみ構築されるため実用上は安全。

#### 課題3: MonadRec 制約

```purescript
runIntent :: forall f m a b. MonadRec m => (f x -> m x) -> Intent f a b -> (a -> m b)
```

スタック安全性のために MonadRec を要求。これにより一部のモナド変換子との組み合わせが制限される。Cloudflare Workers の環境では問題ないが、より複雑なモナドスタックを使う場合は注意が必要。

#### 課題4: Horizont アダプターの不完全実装

Rakuten, Smaregi, Yahoo, Stripe の各アダプターに以下のパターンが見られる：

- `TODO` コメント
- JSON パース部分が stub
- Order processing が未実装

プロトタイプとしては許容範囲だが、本番運用前に完成が必要。

---

### 1.3 総合評価

| 観点 | 評価 | 根拠 |
|------|------|------|
| 理論的整合性 | ◎ | 随伴・Arrow・余積が一貫して適用 |
| 実装の完成度 | △ | Horizont層にstubが残存 |
| 形式検証連携 | ◎ | TLA+ 抽出・フィードバックループ完備 |
| 拡張性 | ○ | Vocabulary追加は余積拡張で対応可 |
| 保守性 | ○ | 層分離明確、依存方向一方向 |

**結論**: 設計に根本的な破綻はない。Intent ⊣ Cognition 随伴は理論的に健全であり、Arrow Effects による分岐禁止も TLA+ 連携と整合している。課題は実装の完成度であり、設計原理自体は堅固。

---

## 2. 既存設計手法との比較

### 2.1 DDD / Clean Architecture との対比

| 概念 | DDD/Clean | Noema | 圏論的意味 |
|------|-----------|-------|-----------|
| Entity | オブジェクト | Subject/Thing | 対象（object） |
| Value Object | 不変オブジェクト | Situs types | 型の inhabitant |
| Repository | 永続化抽象 | Attractor | Presheaf（前層） |
| Service | 手続き集合 | Intent | 自由関手の像 |
| Handler | イベント処理 | Interpretation | 忘却関手 |
| Aggregate | 整合性境界 | Vocabulary coproduct | 余積の成分 |

#### 革新点1: 「実行とは忘却である」

DDD/Clean では「実行」は単に「処理を走らせる」こと。Noema では実行を「構造の忘却」として定式化：

```
Intent（可能性の木）
  ↓ Interpretation（忘却関手）
Factum（単一の事実）
  ↓ collapse
Effect（外界への崩落）
```

Intent は分岐する可能性を保持した構造。Interpretation はその構造を「忘れて」一つの事実に崩落させる。これは量子力学における波動関数の収縮に類似したメタファー。

#### 革新点2: Nomos（法）による時間発展

DDD ではビジネスルールはコードに埋め込まれる。Noema では「法」を一級市民として扱う：

```purescript
type World = { nomosVersion :: NomosVersion, timestamp :: Timestamp }

data Nomos = Nomos
  { version :: NomosVersion
  , rules :: Rules
  , effectiveFrom :: Timestamp
  , supplementaryProvisions :: SupplementaryProvisions  -- 附則
  }

data ConnectionType = Flat | Curved | Critical
```

- **Flat**: 旧法から新法への準同型が存在（スムーズな移行）
- **Curved**: 準同型は存在するが曲率あり（要変換）
- **Critical**: 準同型が存在しない（破壊的変更、過去データの解釈不能）

これにより法改正・仕様変更を数学的に分類できる。

#### 革新点3: Husserl 時間意識

ThingF における時間構造：

```purescript
data ThingF i o
  = GetRetention ThingId Timestamp (Maybe Snapshot -> o)      -- 把持（過去）
  | GetPrimal ThingId (PrimalState -> o)                       -- 原印象（現在）
  | RegisterProtention ThingId PendingIntent (ProtentionId -> o)  -- 予持（未来）
```

- **Retention（把持）**: 過去の Snapshot を参照
- **Primal（原印象）**: 現在の統合状態
- **Protention（予持）**: 将来の Intent を登録（Alarm による実行予約）

DDD の Event Sourcing は「過去」のみ。Noema は「未来」も一級市民として扱う。

---

### 2.2 Effect System との対比

| システム | 分岐 | 合成 | 検証 |
|----------|------|------|------|
| Eff (Haskell) | 許可 | Monad | ランタイム |
| ZIO (Scala) | 許可 | ZIO | 型レベル |
| Algebraic Effects | 許可 | Handler | 継続 |
| **Noema Arrow Effects** | **禁止** | Arrow | **TLA+** |

#### 革新点: 分岐禁止による検証可能性

Arrow Effects は ArrowChoice を実装しないことで、出力に基づく動的分岐を禁止：

```purescript
-- 許可される合成
f >>> g           -- 逐次
f *** g           -- 並列（タプル）
arr (pure func)   -- 純粋関数持ち上げ

-- 禁止される合成（型エラー）
f ||| g           -- 分岐合成（ArrowChoice）
```

この制約により Intent は「操作の列」として静的に決定され、TLA+ Action へ直接マッピング可能：

```
Intent f a b  ↔  Action(vars, vars')
f >>> g       ↔  F ∘ G
f *** g       ↔  F ∧ G
arr f         ↔  vars' = f(vars)
```

---

## 3. 人間とLLMの認知構造

### 3.1 人間の認知: 現象学的構造

Noema の設計は Husserl 現象学に基づく：

```
主体（Ich）─────────────────────▶ 対象（Noema）
    │                                │
    │ 意識作用                        │ 意識内容
    │ (Noesis)                       │ (意味としての対象)
    ▼                                ▼
  Intent                           Thing/Subject
  (意図の構造)                      (意味的対象)
```

#### 人間の認知特性

1. **志向性（Intentionality）**: 意識は常に「何かについての」意識
2. **時間意識**: 過去の把持、現在の原印象、未来の予持
3. **地平構造**: 注目する対象の背後に潜在的可能性が広がる

#### Noema DSL への対応

| 人間の認知 | Noema | 実装 |
|-----------|-------|------|
| 志向性 | Intent | Arrow-based effect |
| 時間意識 | Retention/Primal/Protention | ThingF operations |
| 地平 | Horizont | Channel adapters |
| 沈殿 | Sedimentation | Factum → Seal |

### 3.2 LLM の認知: トランスフォーマーの構造

LLM（Large Language Model）の認知構造は人間とは異なる：

```
入力トークン列 ────▶ Self-Attention ────▶ 出力トークン列
                         │
                    Key-Query-Value
                    (文脈の重み付け)
```

#### LLM の認知特性

1. **並列処理**: 全トークンを同時に「見る」
2. **パターンマッチング**: 統計的な共起関係の学習
3. **コンテキスト窓**: 有限の「作業記憶」
4. **確率的生成**: 次トークンの確率分布から選択

#### Noema との相性

| LLM 特性 | Noema 設計 | 相性 |
|----------|-----------|------|
| コンテキスト窓 | Intent の静的構造 | ◎ 全体を一度に把握可能 |
| パターン認識 | Vocabulary の一貫性 | ◎ 語彙パターンを学習 |
| 確率的生成 | Arrow の決定論 | △ LLM は分岐を好むが禁止 |
| 並列処理 | `***` 並列合成 | ○ 並列性を表現可能 |

#### LLM との協働における利点

1. **CLAUDE.md による文脈共有**: LLM はドキュメントから設計意図を理解
2. **一貫した語彙**: Subject, Thing, Relation, Contract という4語彙
3. **圏論的メタ言語**: 随伴、関手、自然変換という普遍的概念
4. **形式仕様の明示**: TLA+ との対応が明文化

---

## 4. 意味論の文脈

### 4.1 操作的意味論 vs 表示的意味論

#### 操作的意味論（Operational Semantics）

「プログラムがどう実行されるか」を規定：

```
⟨GetStock pid sid, σ⟩ → ⟨v, σ⟩
  where v = σ.inventory[pid][sid]
```

Noema では Interpretation が操作的意味論を与える：

```purescript
interpretInventoryF :: InventoryEnv -> Interpretation InventoryF
interpretInventoryF env = case _ of
  GetStock pid sid k -> do
    result <- recognize $ queryStock env.sql pid sid
    pure (k result)
```

#### 表示的意味論（Denotational Semantics）

「プログラムが何を意味するか」を数学的対象にマッピング：

```
⟦Intent f a b⟧ : ⟦a⟧ → ⟦b⟧
⟦f >>> g⟧ = ⟦g⟧ ∘ ⟦f⟧
⟦f *** g⟧ = ⟦f⟧ × ⟦g⟧
```

Noema では Arrow laws が表示的意味論を保証：

```purescript
-- Identity
arr id >>> f ≡ f
f >>> arr id ≡ f

-- Association
(f >>> g) >>> h ≡ f >>> (g >>> h)

-- First/Second laws
first (arr f) ≡ arr (first f)
first (f >>> g) ≡ first f >>> first g
```

### 4.2 随伴意味論（Adjoint Semantics）

Noema の革新は「随伴」を意味論の基盤とすること：

```
Hom_Struct(Intent(P), S) ≅ Hom_Prop(P, Cognition(S))
```

「命題 P から構造 S を意図する道筋」と「構造 S を認知して命題 P を理解する道筋」は自然に対応する。

#### 単位と余単位

```
η : Id_Prop ⇒ Cognition ∘ Intent    （単位）
ε : Intent ∘ Cognition ⇒ Id_Struct  （余単位）
```

- **η（単位）**: 純粋な命題が意図され、実行されて事実として戻る
- **ε（余単位）**: 認知に基づいて意図し、その意図が構造に着地する

### 4.3 Vorzeichnungsschema の意味論

```
Vorzeichnung = Freer f = Free(Coyoneda f)
```

Coyoneda は左 Kan 拡張による自由関手構成：

```
Coyoneda f = Lan_Y f
```

これにより任意の型構成子 f を「関手化」できる。Intent は「まだ整っていない意図が構造化される過程」を含む。

---

## 5. 形式手法の文脈

### 5.1 TLA+ 統合

#### 抽出パイプライン

```
PureScript Intent
      ↓ Extract.purs
TLA+ Module
      ↓ TLC Model Checker
Counter Example (or ✓)
      ↓ Feedback.purs
PureScript Test / GitHub Issue
```

#### 対応表

| PureScript | TLA+ |
|------------|------|
| `Intent f a b` | `Action` |
| `f >>> g` | `F ∘ G` |
| `f *** g` | `F ∧ G` |
| `arr f` | `vars' = f(vars)` |
| `Vocabulary` | `VARIABLES` |
| `Handler guard` | `ENABLED` |

#### 検証される性質

```tla
NonNegativeStock == \A p \in ProductIds, l \in LocationIds:
  stock[p][l] >= 0

ReservationBound == \A p \in ProductIds, l \in LocationIds:
  reserved[p][l] <= stock[p][l]

TypeInvariant == /\ stock \in [ProductIds -> [LocationIds -> 0..MaxQuantity]]
                 /\ reserved \in [ProductIds -> [LocationIds -> 0..MaxQuantity]]
```

### 5.2 フィードバックループ

TLC が反例を発見した場合：

```purescript
-- Feedback.purs が生成するテストコード
describe "TLA+ Counterexample: NonNegativeStock violated" do
  it "reproduces the violation" do
    let intent = adjustStock (ThingId "SKU-001") (SubjectId "loc-01") (QuantityDelta (-100))
    result <- runTest intent
    result `shouldSatisfy` isLeft
```

これにより形式検証と実装テストが連動する。

### 5.3 Nomos と Connection 検証

法（Nomos）の変更時に整合性を検証：

```purescript
data ConnectionType
  = Flat          -- 準同型あり（スムーズ移行）
  | Curved        -- 準同型あり・曲率あり（要変換）
  | Critical      -- 準同型なし（破壊的変更）

verifyConnection :: Nomos -> Nomos -> ConnectionType
```

- **Flat の場合**: 旧 Seal を新 Nomos で再解釈可能
- **Curved の場合**: 変換関数を附則として提供
- **Critical の場合**: 過去データの意味が失われる（警告必須）

---

## 6. 結論

### Noema の位置づけ

```
                    抽象度
                      ↑
        圏論 ────────●──────── 数学
                     │
           Noema ────●──────── DSL
                     │
      DDD/Clean ─────●──────── 設計パターン
                     │
    PureScript ──────●──────── 実装言語
                     │
Cloudflare Workers ──●──────── ランタイム
                      ↓
                    具象度
```

### まとめ

| 観点 | 結論 |
|------|------|
| 設計の健全性 | 随伴構造は数学的に well-defined |
| 革新性 | 「実行＝忘却」「法のバージョニング」「時間の三相」 |
| 実用性 | TLA+ 連携により形式検証と実装が連動 |
| LLM 親和性 | 一貫した語彙と圏論的メタ言語 |
| 課題 | Horizont 層の実装完成、FreerArrow.purs の整理 |

Noema は「意味論」と「形式手法」を圏論という共通言語で統合し、人間とLLMの両方が理解可能な DSL を目指す実験的プロジェクトである。

---

## 付録: 用語集

| 用語 | 由来 | Noema での意味 |
|------|------|---------------|
| Noema | Husserl 現象学 | 意識内容としての意味的対象 |
| Vorzeichnung | ドイツ語「予描」 | 実行前の意志構造 |
| Cognition | ラテン語「認識」 | 構造を事実に崩落させる解釈 |
| Factum | ラテン語「為されたこと」 | 解釈結果としての事実 |
| Sedimentation | 現象学「沈殿」 | 事実の不可逆的確定 |
| Horizont | ドイツ語「地平」 | 外界との境界 |
| Nomos | ギリシャ語「法」 | ビジネスルールの形式化 |
| Attractor | 力学系「引き込み領域」 | 状態を集約する Durable Object |

---

## 参考文献

- Sanada, K. (2023). "Algebraic effects and handlers for arrows"
- Husserl, E. "Ideen zu einer reinen Phänomenologie und phänomenologischen Philosophie"
- Lamport, L. "Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers"
- Hughes, J. (2000). "Generalising Monads to Arrows"
