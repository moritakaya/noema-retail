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
│  ├── Freer.purs                   ├── Handler.purs              │
│  └── Vocabulary/                  └── Collapse.purs             │
│      └── RetailF                                                │
│           │                              │                      │
│           ▼ Free F                       ▼ U (忘却)              │
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
│   ├── Vorzeichnung/               # 予描図式 = Free F（左随伴）
│   │   ├── Freer.purs              # Freer Monad
│   │   └── Vocabulary/             # 語彙 = Functor F
│   │       ├── Base.purs           # 基本型・識別子
│   │       ├── InventoryF.purs     # 在庫操作
│   │       ├── HttpF.purs          # HTTP 操作
│   │       ├── StorageF.purs       # Storage 操作
│   │       └── RetailF.purs        # 余積 Σ Vocabulary
│   │
│   ├── Cognition/                  # 認知 = Forgetful U（右随伴）
│   │   ├── Collapse.purs           # Intent → Effect の解釈
│   │   ├── InventoryHandler.purs   # 在庫 Handler
│   │   └── StorageHandler.purs     # Storage Handler
│   │
│   ├── Sedimentation/              # 沈殿 = 状態の定着
│   │   ├── Attractor.purs          # 抽象 Attractor
│   │   ├── Seal.purs               # 封印（トランザクション結果）
│   │   └── Cryostasis.purs         # 凍結（Alarm 待機）
│   │
│   └── Presheaf/                   # 表現 = Channel^op → Set
│       ├── Channel.purs            # Channel 圏の対象
│       ├── ChannelAdapter.purs     # 基底型クラス
│       ├── Smaregi.purs            # スマレジ連携
│       ├── Rakuten.purs            # 楽天市場連携
│       ├── Yahoo.purs              # Yahoo!連携
│       └── Stripe.purs             # Stripe 連携
│
└── Platform/                       # プラットフォーム実装
    └── Cloudflare/
        ├── InventoryAttractor.purs # Attractor の DO 実装
        ├── Router.purs             # Hono ルーター
        └── FFI/                    # Workers 固有 API
            ├── DurableObject.purs
            ├── SqlStorage.purs
            ├── Fetch.purs
            ├── Crypto.purs
            ├── Request.purs
            └── Response.purs
```

## 技術スタック

| 層 | 技術 | 圏論的役割 |
|---|---|---|
| **DSL** | PureScript | Free F（Vorzeichnung） |
| **Handler** | PureScript | A-algebra（Cognition） |
| **Runtime** | TypeScript/JS | Carrier（台） |
| **State** | Durable Objects + SQLite | Sedimentation |
| **Gateway** | Hono | 外界との接点 |

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
spago test --main Test.Noema.Vorzeichnung  # Functor/Monad 法則
spago test --main Test.Noema.Cognition     # Handler 準同型
spago test --main Test.Noema.Presheaf      # 自然変換
npm run test:integration                    # 統合テスト
```

## 設計原則

1. **随伴の保存**: Vorzeichnung/ ⊣ Cognition/ が明示的
2. **関手の局所性**: 語彙は Vocabulary/ に集約
3. **技術非依存**: Noema/ は Platform/ に依存しない
4. **Presheaf として在庫**: Inventory : Channel^op → Set

## 日本語で応答してください
