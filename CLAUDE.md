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
│  ├── FreerArrow.purs              ├── Handler.purs              │
│  └── Vocabulary/                  └── InventoryHandler.purs     │
│      └── InventoryF                                             │
│           │                              │                      │
│           ▼ Arrow Effects               ▼ U (忘却)              │
│       Intent ────────────────────────▶ Effect                   │
│      (意志の構造)                       (事実)                   │
│                                          │                      │
│                                          ▼                      │
│                                 Sedimentation/                  │
│                                 └── Attractor                   │
│                                     (沈殿)                       │
│                                          │                      │
│                                          ▼                      │
│                                 Presheaf/                       │
│                                 Channel^op → Set                │
│                                 (外界への表現)                   │
└─────────────────────────────────────────────────────────────────┘
```

## ディレクトリ構造

```
src/
├── Main.purs                       # Worker エントリーポイント
│
├── Noema/                          # Noema DSL 本体
│   │
│   ├── Vorzeichnung/               # 予描図式 = Arrow Effects（左随伴）
│   │   ├── Intent.purs             # Arrow-based Intent
│   │   ├── FreerArrow.purs         # Freer Arrow 実装
│   │   ├── Combinators.purs        # Arrow コンビネータ
│   │   └── Vocabulary/             # 語彙 = Functor F
│   │       ├── Base.purs           # 基本型・識別子
│   │       ├── InventoryF.purs     # 在庫操作
│   │       ├── HttpF.purs          # HTTP 操作
│   │       ├── StorageF.purs       # Storage 操作
│   │       └── RetailF.purs        # 余積 Σ Vocabulary
│   │
│   ├── Cognition/                  # 認知 = Forgetful U（右随伴）
│   │   ├── Handler.purs            # Handler 基底型
│   │   ├── InventoryHandler.purs   # 在庫 Handler
│   │   └── StorageHandler.purs     # Storage Handler
│   │
│   ├── Sedimentation/              # 沈殿 = 状態の定着
│   │   ├── Attractor.purs          # 抽象 Attractor
│   │   ├── Seal.purs               # 封印（トランザクション結果）
│   │   └── Cryostasis.purs         # 凍結（Alarm 待機）
│   │
│   └── Presheaf/                   # 表現 = Channel^op → Set
│       ├── ChannelAdapter.purs     # 基底型クラス
│       ├── Smaregi.purs            # スマレジ連携
│       ├── Rakuten.purs            # 楽天市場連携
│       └── Stripe.purs             # Stripe 連携
│
├── Control/                        # Arrow 制御構造
│   └── Arrow.purs                  # Arrow 型クラス
│
├── TlaPlus/                        # TLA+ 連携
│   ├── Extract.purs                # Intent → TLA+ 抽出
│   └── Feedback.purs               # TLA+ 結果フィードバック
│
└── Platform/                       # プラットフォーム実装
    └── Cloudflare/
        ├── InventoryAttractor.purs # Attractor の DO 実装
        ├── Router.purs             # Hono ルーター
        └── FFI/                    # Workers 固有 API
            ├── DurableObject.purs
            ├── SqlStorage.purs
            └── ...
```

## 技術スタック

| 層 | 技術 | 圏論的役割 |
|---|---|---|
| **DSL** | PureScript | Arrow Effects（Vorzeichnung） |
| **Handler** | PureScript | A-algebra（Cognition） |
| **Runtime** | TypeScript/JS | Carrier（台） |
| **State** | Durable Objects + SQLite | Sedimentation |
| **Gateway** | Hono | 外界との接点 |
| **Verification** | TLA+ | 形式的モデル検証 |

## コマンド

```bash
# 開発
spago build           # PureScript ビルド
npm run build         # ESBuild バンドル
wrangler dev          # ローカル起動

# デプロイ
wrangler deploy                    # 開発環境
wrangler deploy --env production   # 本番環境

# テスト
spago test            # Arrow 法則テスト

# TLA+ 検証
cd tlaplus/specs
java -jar ~/tla2tools.jar -config InventorySimple.cfg InventorySimple.tla
```

## 設計原則

1. **随伴の保存**: Vorzeichnung/ ⊣ Cognition/ が明示的
2. **関手の局所性**: 語彙は Vocabulary/ に集約
3. **技術非依存**: Noema/ は Platform/ に依存しない
4. **Presheaf として在庫**: Inventory : Channel^op → Set
5. **Arrow Effects**: 分岐禁止（ArrowChoice なし）

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
| Cognition | 意図の解釈・実行 | Handler |
| Vorzeichnung | 前描画スキーマ | - |
| Vocabulary | ドメイン語彙 | Domain Model |
| Arrow Effects | 分岐禁止の効果系 | Effect System |

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
Thing（物）: 意志を持たない → Guardian Subject に包摂される
```

### グロタンディーク構成

```
Locus = 空間座標（DO の ID）
World = 法座標（Nomos のバージョン）

Base 圏: DO のネットワーク（水平射 = RPC）
Fiber 圏: DO 内の状態空間（垂直射 = Sediment）
```

### Thing = Guardian の不変量

Thing 自体は DO ではない。Guardian DO が Thing を「包摂」する。
- Thing の同一性 = Guardian DO の id
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
2. **Arrow 維持**: ArrowChoice 禁止、分岐は Handler で
3. **Source of Truth**: 所有権等は Thing Guardian が保持
4. **View**: Container の Contents はキャッシュ
