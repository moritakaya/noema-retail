# Noema Retail

圏論的基盤に基づく分散システム DSL。Intent（意図）と Cognition（認知）の随伴関係により、副作用の構造と実行を分離する。

## 設計原理

### Intent ⊣ Cognition 随伴

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

- **Intent**: 「何をしたいか」の静的構造（Arrow Effects）
- **Cognition**: 「どう実行するか」の動的解釈（Handler）
- **Vorzeichnung（前描画）**: 実行前に Intent の全構造が確定。「実行は忘却である」

### Arrow Effects（分岐禁止）

- ArrowChoice を意図的に実装しない
- 分岐は Cognition（Handler）の責務
- TLA+ でのモデル検証が容易

## ディレクトリ構造

```
src/
├── Main.purs                       # Worker エントリーポイント
│
├── Noema/                          # Noema DSL 本体
│   ├── Core/                       # 基本型と座標系
│   │   ├── Locus.purs              # 空間座標（SubjectId, ThingId 等）
│   │   └── World.purs              # 法座標（Nomos, Context）
│   │
│   ├── Vorzeichnung/               # 意図の構造（左随伴）
│   │   ├── Intent.purs             # Arrow-based Intent
│   │   ├── FreerArrow.purs         # Arrow 実装
│   │   ├── Combinators.purs        # Arrow コンビネータ
│   │   └── Vocabulary/             # ドメイン語彙
│   │       ├── SubjectF.purs       # 意志主体操作
│   │       ├── ThingF.purs         # もの・こと操作
│   │       ├── RelationF.purs      # 関係操作
│   │       ├── ContractF.purs      # 契約操作
│   │       ├── NoemaF.purs         # 統合語彙（余積）
│   │       ├── Constructors.purs   # スマートコンストラクタ
│   │       ├── InventoryF.purs     # 在庫操作
│   │       ├── HttpF.purs          # HTTP 操作
│   │       ├── StorageF.purs       # Storage 操作
│   │       └── RetailF.purs        # レガシー余積
│   │
│   ├── Cognition/                  # 認知・実行（右随伴）
│   │   ├── Handler.purs            # Handler 基底型
│   │   ├── InventoryHandler.purs   # 在庫 Handler
│   │   └── StorageHandler.purs     # Storage Handler
│   │
│   ├── Sedimentation/              # 沈殿（状態の定着）
│   │   ├── Attractor.purs          # 抽象 Attractor
│   │   └── Seal.purs               # 封印（トランザクション結果）
│   │
│   └── Presheaf/                   # 表現（Channel^op → Set）
│       ├── Channel.purs            # Channel 圏の対象
│       ├── ChannelAdapter.purs     # 基底型クラス
│       ├── Smaregi.purs            # スマレジ連携
│       ├── Rakuten.purs            # 楽天市場連携
│       ├── Yahoo.purs              # Yahoo!ショッピング連携
│       └── Stripe.purs             # Stripe 連携
│
├── Control/                        # Arrow 制御構造
│   └── Arrow.purs                  # Arrow 型クラス実装
│
├── TlaPlus/                        # TLA+ 連携
│   ├── Extract.purs                # Intent → TLA+ 抽出
│   └── Feedback.purs               # TLA+ 検証結果フィードバック
│
└── Platform/                       # プラットフォーム実装
    └── Cloudflare/
        ├── InventoryAttractor.purs # Attractor の DO 実装
        ├── Router.purs             # Hono ルーター
        └── FFI/                    # Workers 固有 API
            ├── DurableObject.purs  # DO 基本操作
            ├── SqlStorage.purs     # SQLite Storage
            ├── Request.purs        # Request 操作
            ├── Response.purs       # Response 操作
            ├── Fetch.purs          # Fetch API
            └── Crypto.purs         # 暗号操作

tlaplus/
└── specs/                          # TLA+ 形式検証
    ├── InventorySimple.tla         # 在庫操作仕様
    └── InventorySimple.cfg         # TLC 設定
```

## 圏論的対応

| 概念 | PureScript | TLA+ |
|------|------------|------|
| 逐次合成 | `f >>> g` | F ∘ G |
| 並列合成 | `f *** g` | F ∧ G |
| 純粋変換 | `arr f` | vars' = f(vars) |
| 効果 | `liftEffect` | Action |

## コマンド

```bash
# ビルド
spago build

# テスト
spago test

# TLA+ 検証
cd tlaplus/specs
java -jar ~/tla2tools.jar -config InventorySimple.cfg InventorySimple.tla

# 開発
npm run build      # ESBuild バンドル
wrangler dev       # ローカル起動

# デプロイ
wrangler deploy                    # 開発環境
wrangler deploy --env production   # 本番環境
```

## 開発ガイド

- [設計原理](docs/design-principles.md)
- [Intent 記述ガイド](src/Noema/Vorzeichnung/README.md)
- [Handler 実装ガイド](src/Noema/Cognition/README.md)
- [TLA+ 検証](tlaplus/README.md)

## API エンドポイント

### 在庫操作

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/inventory/:productId/:subjectId` | GET | 在庫取得（Thing × Subject） |
| `/api/inventory/:productId` | GET | 在庫取得（デフォルト Subject） |
| `/api/inventory` | POST | 在庫作成/更新 |
| `/api/adjust` | POST | 在庫調整 |
| `/api/reserve` | POST | 在庫予約 |
| `/api/reserve/:reservationId` | DELETE | 予約解放 |

### 同期・ログ

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/sync/:productId` | GET | 同期状態取得 |
| `/api/log/:productId` | GET | 在庫変動ログ取得 |

> 注: `subjectId` は Subject（倉庫、店舗など）を識別する。Thing は Subject に包摂される。
> 旧 API の `locationId` は `subjectId` に統合された。

## セットアップ

### 環境変数設定

```bash
# Stripe
wrangler secret put STRIPE_API_KEY
wrangler secret put STRIPE_WEBHOOK_SECRET

# 楽天市場
wrangler secret put RAKUTEN_SERVICE_SECRET
wrangler secret put RAKUTEN_LICENSE_KEY

# スマレジ
wrangler secret put SMAREGI_CLIENT_SECRET
wrangler secret put SMAREGI_ACCESS_TOKEN
```
