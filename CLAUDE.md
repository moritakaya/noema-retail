# Noema Retail Backend

小売業基幹システムのための DSL。圏論的随伴構造を基盤とする分散システム。

## 哲学的基盤

> **プログラムとは、主体が世界に対して投げかける意志を、Vorzeichnungsschema として構造化し、認知（Cognition）による忘却を通じて事実へと崩落させる、対話的運動である。**

> **実行とは忘却である。**

## 圏論的構造

```
┌─────────────────────────────────────────────────────────────────┐
│                      随伴 F ⊣ U                                 │
│                                                                 │
│  Vorzeichnung/          ⊣         Cognition/                   │
│  ├── FreerArrow.purs              └── Interpretation.purs       │
│  └── Vocabulary/                                                │
│      └── InventoryF                                             │
│           │                              │                      │
│           ▼ Arrow Effects               ▼ U (忘却)              │
│       Intent ────────────────────────▶ Factum                   │
│      (意志の構造)                       (事実)                   │
│                                          │                      │
│                                          ▼                      │
│                                 Sedimentation/                  │
│                                 ├── Factum    (流動的事実)      │
│                                 └── Seal      (確定した事実)    │
│                                    ※ Attractor = DO（沈殿の場） │
│                                          │                      │
│                                          ▼ collapse (忘却)      │
│                                       Effect                    │
│                                     (外界への崩落)               │
│                                          │                      │
│                                          ▼                      │
│                                 Horizont/                       │
│                                 Channel^op → Set                │
│                                 (外界との地平線)                 │
└─────────────────────────────────────────────────────────────────┘
```

### Sedimentation 層の構造

```
Sedimentation/（沈殿）
├── Factum.purs      -- 解釈の結果（まだ流動的な事実）
└── Seal.purs        -- 沈殿の証明（確定した事実）

流れ:
  Factum（液体）→ DO.sediment（沈殿過程）→ Seal（固体）→ collapse → Effect
  ※ DO = InventoryAttractor 等の Durable Object（Attractor として機能）
```

### 技術的語彙から哲学的語彙への移行

| 旧名称 | 新名称 | 理由 |
|--------|--------|------|
| Handler | **Interpretation** | 現象学の「解釈」(Auslegung) |
| Effect | **Factum** | ラテン語「為されたこと」= 事実 |

**動機**: 技術は進歩し変化する（Algebraic Effects 等）が、哲学・意味論は安定している。
Noema の語彙体系（Topos, Horizont, Vorzeichnung, Cognition, Sedimentation）と整合させた。

## モノレポ構成

このリポジトリは spago workspace を使用したモノレポ構成です。

| パッケージ | 説明 | 依存 |
|------------|------|------|
| `noema-core` | DSL コア（Intent, Arrow, AVDC 語彙） | - |
| `noema-retail` | 小売業実装（在庫、チャネルアダプター、Platform） | `noema-core` |

### パッケージ分離の原則

```
noema-core (DSL)              noema-retail (実装)
├── Arrow 型クラス            ├── InventoryF（ドメイン語彙）
├── Intent / Interpretation   ├── HttpF / StorageF（インフラ）
├── AVDC 語彙                 ├── Interpretations（具体実装）
│   ├── SubjectF              │   ├── InventoryInterpretation
│   ├── ThingF                │   └── StorageInterpretation
│   ├── RelationF             ├── Horizont/（チャネル実装）
│   ├── ContractF             │   ├── Channel, InventoryCarrier
│   └── NoemaF                │   └── Rakuten, Smaregi, Yahoo, Stripe
├── Topos/Situs, Nomos, Presheaf
├── Horizont/Carrier  # 外的地平線（担体）
├── Sedimentation/Factum, Seal
└── Platform/Cloudflare/
    ├── FFI, Router  # 汎用インフラ
    └── InventoryAttractor（Retail固有DO）  # noema-retail
```

**依存方向**: `noema-retail` → `noema-core`（逆方向は禁止）

## ディレクトリ構造

```
packages/
├── noema-core/                    # DSL コア
│   ├── src/
│   │   ├── Control/Arrow.purs     # Arrow 型クラス
│   │   ├── Noema/
│   │   │   ├── Topos/             # トポス構造（内的）
│   │   │   │   ├── Situs.purs     # 空間座標（Site の点）
│   │   │   │   ├── Nomos.purs     # 法座標（被覆構造）
│   │   │   │   └── Presheaf.purs  # ステージング（前層）
│   │   │   ├── Horizont/          # 地平線（外的）
│   │   │   │   └── Carrier.purs   # 外部接続の担体
│   │   │   ├── Vorzeichnung/      # 予描図式（左随伴）
│   │   │   │   ├── Intent.purs    # Arrow-based Intent
│   │   │   │   ├── FreerArrow.purs
│   │   │   │   ├── Combinators.purs
│   │   │   │   └── Vocabulary/    # AVDC 語彙
│   │   │   │       ├── SubjectF.purs
│   │   │   │       ├── ThingF.purs
│   │   │   │       ├── RelationF.purs
│   │   │   │       ├── ContractF.purs
│   │   │   │       └── NoemaF.purs
│   │   │   ├── Cognition/
│   │   │   │   └── Interpretation.purs   # 解釈（f ~> Factum）
│   │   │   └── Sedimentation/
│   │   │       ├── Factum.purs    # 流動的事実（newtype Factum a = Factum (Effect a)）
│   │   │       └── Seal.purs      # 確定した事実
│   │   └── Platform/Cloudflare/   # 汎用 Cloudflare インフラ
│   │       ├── Router.purs        # HTTP ルーター
│   │       └── FFI/               # Workers API バインディング
│   │           ├── DurableObject.purs
│   │           ├── Request.purs
│   │           ├── Response.purs
│   │           ├── SqlStorage.purs
│   │           ├── Fetch.purs
│   │           └── Crypto.purs
│   └── spago.yaml
│
└── noema-retail/                  # 小売実装
    ├── src/
    │   ├── Main.purs              # Worker エントリーポイント
    │   ├── Noema/
    │   │   ├── Vorzeichnung/Vocabulary/
    │   │   │   ├── InventoryF.purs
    │   │   │   ├── HttpF.purs
    │   │   │   └── StorageF.purs
    │   │   └── Cognition/
    │   │       ├── InventoryInterpretation.purs  # 在庫操作の解釈
    │   │       └── StorageInterpretation.purs    # ストレージ操作の解釈
    │   ├── Horizont/                  # 外部チャネル Carrier 実装
    │   │   ├── Channel.purs           # Channel 基底圏の対象
    │   │   ├── InventoryCarrier.purs  # 在庫用 Carrier 型クラス
    │   │   ├── Rakuten.purs
    │   │   ├── Smaregi.purs
    │   │   ├── Yahoo.purs
    │   │   └── Stripe.purs
    │   ├── TlaPlus/
    │   │   ├── Extract.purs
    │   │   └── Feedback.purs
    │   └── Platform/Cloudflare/
    │       └── InventoryAttractor.purs  # Retail 固有の DO
    ├── worker.js                  # Cloudflare Workers エントリーポイント
    └── spago.yaml
```

## 技術スタック

| 層 | 技術 | 圏論的役割 |
|---|---|---|
| **DSL** | PureScript | Arrow Effects（Vorzeichnung） |
| **Interpretation** | PureScript | A-algebra homomorphism（Cognition） |
| **Factum** | PureScript | 流動的事実（Sedimentation） |
| **Runtime** | TypeScript/JS | 台（carrier）→ Effect |
| **State** | Durable Objects + SQLite | Sedimentation（Attractor） |
| **Horizont** | Hono | 外界との地平線（Carrier） |
| **Verification** | TLA+ | 形式的モデル検証 |

## コマンド

```bash
# ビルド
spago build                     # 全パッケージビルド
spago build -p noema-core       # DSL コアのみ
spago build -p noema-retail     # 小売実装のみ

# テスト
spago test                      # 全パッケージテスト
spago test -p noema-core        # Arrow 法則テスト
spago test -p noema-retail      # 小売実装テスト

# 開発
npm run build                   # ESBuild バンドル
wrangler dev                    # ローカル起動

# デプロイ
wrangler deploy                    # 開発環境
wrangler deploy --env production   # 本番環境

# TLA+ 検証
cd tlaplus/specs
java -jar ~/tla2tools.jar -config InventorySimple.cfg InventorySimple.tla
```

## 設計原則

1. **随伴の保存**: Vorzeichnung/ ⊣ Cognition/ が明示的
2. **関手の局所性**: 語彙は Vocabulary/ に集約
3. **技術非依存**: Noema/ は Platform/ に依存しない
4. **Horizont として在庫**: Inventory : Channel^op → Set（外部システム連携）
5. **Arrow Effects**: 分岐禁止（ArrowChoice なし）
6. **Topos / Horizont 対称性**: 内的構造（Topos）と外的地平線（Horizont）の分離

---

# Noema Documentation Policy

## ドキュメント方針

Noema は既存の設計手法（DDD, Clean Architecture 等）に依存しない、
圏論的基盤に基づく DSL である。自然言語による設計書を重視する。

### 必須ルール

1. **新規ディレクトリには必ず README.md を配置**
   - ディレクトリ作成と同時に README.md もコミット
   - 空のディレクトリは許可しない

2. **README.md の必須セクション**
   ```markdown
   # [ディレクトリ名]

   ## 役割
   このモジュールの責務を1-2文で説明。

   ## 圏論的位置づけ
   - どの圏に属するか（Intent圏、Cognition圏、etc）
   - 他モジュールとの関手的関係
   - 随伴関係があれば明記

   ## 主要コンポーネント
   - `File.purs`: 説明

   ## 使用例
   ```purescript
   example = ...
   ```
   ```

3. **圏論的記述を優先**
   - 使う: Intent, Cognition, Vorzeichnung, 随伴, 関手, 自然変換
   - 避ける: Entity, Repository, Service, Aggregate, UseCase

4. **コミットメッセージ**
   - ディレクトリ追加時: `docs:` プレフィックスで README も言及
   - 例: `feat(inventory): Add reservation module with docs`

### ドキュメント階層

```
/
├── README.md              # プロジェクト全体概要
├── CLAUDE.md              # AI向けガイドライン（このファイル）
├── docs/
│   ├── design-principles.md   # 設計原理詳細
│   └── tla-pipeline.md        # TLA+検証
├── src/
│   └── [Module]/
│       └── README.md      # 各モジュールの説明
└── tlaplus/
    └── README.md          # TLA+仕様の説明
```

### Noema 固有の用語

| Noema用語 | 意味 | DDD等価物（参考のみ） |
|-----------|------|----------------------|
| Intent | 意図の静的構造 | Command/Query |
| Cognition | 意図の解釈の場 | - |
| **Interpretation** | Intent の解釈（f ~> Factum） | Handler |
| **Factum** | 流動的事実（事実として認識されたもの） | Effect の哲学的対応物 |
| Vorzeichnung | 前描画スキーマ | - |
| Vocabulary | ドメイン語彙 | Domain Model |
| Arrow Effects | 分岐禁止の効果系 | Effect System |
| Topos | 内的論理空間 | - |
| Horizont | 外界との地平線 | Gateway |
| Carrier | 外部接続の担体（noema-core） | Adapter |
| InventoryCarrier | 在庫用 Carrier（noema-retail） | Inventory Adapter |
| **collapse** | Factum → Effect（忘却） | unsafePerformEffect |
| **recognize** | Effect → Factum（認識） | liftEffect |

### 設計書更新のトリガー

以下の変更時は必ず関連ドキュメントを更新：
- 新規モジュール追加
- 公開 API の変更
- 圏論的構造の変更
- TLA+ 仕様の追加・変更

---

## 補足: なぜ自然言語の設計書を重視するか

1. **LLM との協働**: AI がコードベースを理解しやすくなる
2. **圏論的構造の明示**: 型だけでは伝わらない設計意図を補完
3. **知識の永続化**: 開発者の交代に備える
4. **TLA+ との対応**: 形式仕様と実装の対応を記述

## 日本語で応答してください
# Vocabulary 設計ガイド（CLAUDE.md 追加セクション）

## Vocabulary の哲学的基盤

### 存在論的三層

```
Nomos（大域意志）: 法律、商習慣 → Sediment の解釈を規定
Subject（主体）: 意志を持つ → DO として実装
Thing（物）: 意志を持たない → Subject に包摂される
```

### グロタンディーク構成（Topos）

```
Situs = 空間座標（Site の点、DO の ID）
Nomos = 法座標（本則 + 附則）
World = (NomosVersion, region, timestamp)
Presheaf = 前層（ステージング環境）

Base 圏: DO のネットワーク（水平射 = RPC）
Fiber 圏: DO 内の状態空間（垂直射 = Sediment）
Presheaf → Sheaf: 層化関手（Sedimentation）
```

### Nomos（法の構造）

```purescript
type Nomos =
  { version :: NomosVersion
  , rules :: Rules                    -- 本則（将来は Lean4 で検証）
  , supplementary :: SupplementaryProvisions  -- 附則
  , predecessor :: Maybe NomosVersion
  }

type SupplementaryProvisions =
  { effectiveFrom :: Timestamp        -- 施行日
  , existingContracts :: ContractTransition
  , gracePeriod :: Maybe Duration
  , exceptions :: Array ExceptionRule
  }

data ContractTransition = PreserveOldLaw | MigrateToNewLaw | CaseByCase
```

### Connection（位相論的接続）

Nomos バージョン間の「連続的な平行移動」を検証する。

| 分類 | 意味 | 例 |
|------|------|-----|
| Flat | 連続的移行可能 | ドキュメント修正、パフォーマンス改善 |
| Curved | 非連続、警告を伴う | 予約上限の変更、スキーマの追加 |
| Critical | 即時適用必須 | セキュリティパッチ、法令対応 |

### 判例（Case Law）

Noema には「エラー」という概念はない。
Cognition が正常に崩落しなかったケースは「判例」として記録される。

```purescript
data StagingOutcome
  = Sedimented SedimentId World  -- 正常に沈殿
  | Abandoned                     -- ユーザーによる取り消し
  | Rejected World Reason         -- 判例
```

判例は将来の Nomos 改訂（立法）に影響を与える。

### Thing = Subject の包摂

Thing 自体は DO ではない。Subject が Thing を「包摂」する。
- Thing の同一性 = 包摂する Subject の id
- Thing の状態 = Sediment の積分値

## 四つの語彙

```purescript
type NoemaF = Coproduct4 SubjectF ThingF RelationF ContractF
```

| 語彙 | 圏論的位置 | 操作対象 |
|------|-----------|---------|
| SubjectF | Base 圏 | 意志を持つ主体 |
| ThingF | Fiber 圏 | もの・こと（属性×位置×時間）|
| RelationF | Span 圏 | Subject-Thing 間の関係 |
| ContractF | 規定の圏 | 権利・義務、契約間関係 |

## ThingF の時間構造（Husserl）

```
Retention（把持）: 過去の Snapshot
Primal（原印象）: 現在の状態
Protention（予持）: 未来の Pending Intent
```

## RelationKind 一覧

```
包摂: Contains, Guards
権利: Owns, Possesses, Claims, Secures, SharedBy
引当: Reserves, Commits, Intends
移動: Transports, Consigns
構成: ComposedOf, BundledWith, Substitutes
観測: Observes, Tracks
代理: ActsFor
制限: Restricts
```

## Contract 間の関係

```
Prerequisite（前提）: B は A がないと成立しない
Subordinate（従属）: A 終了で B も終了
Consideration（対価）: A の履行が B の対価
Security（担保）: B は A の履行を担保
Amendment（変更）: B は A を変更
Termination（解除）: B は A を解除
```

## 実装規則

1. **Sediment のみ**: UPDATE 禁止、INSERT のみ
2. **Arrow 維持**: ArrowChoice 禁止、分岐は Interpretation で
3. **Source of Truth**: 所有権等は Thing を包摂する Subject が保持
4. **View**: Container の Contents はキャッシュ
5. **FFI 境界**: Effect は recognize で Factum に、エントリーポイントで collapse
