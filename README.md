# Noema Retail

圏論的基盤に基づく分散システム DSL。Intent（意図）と Cognition（認知）の随伴関係により、副作用の構造と実行を分離する。

## 設計原理

### Intent ⊣ Cognition 随伴

```
┌─────────────────────────────────────────────────────────────────┐
│                      随伴 F ⊣ U                                 │
│                                                                 │
│  Vorzeichnung/          ⊣         Cognition/                   │
│  ├── Intent.purs                  └── Interpretation.purs       │
│  └── Vocabulary/                                                │
│      └── InventoryF, SubjectF                                   │
│           │                              │                      │
│           ▼ Arrow Effects               ▼ U (忘却)              │
│       Intent ────────────────────────▶ Effect                   │
│      (意志の構造)                       (事実)                   │
│                                          │                      │
│                                          ▼                      │
│                                 Sedimentation/                  │
│                                 └── Factum → Seal               │
│                                     (沈殿)                       │
│                                          │                      │
│                                          ▼                      │
│                                 Horizont/                       │
│                                 Channel^op → Set                │
│                                 (外界との地平線)                 │
└─────────────────────────────────────────────────────────────────┘
```

- **Intent**: 「何をしたいか」の静的構造（Arrow Effects）
- **Cognition**: 「どう実行するか」の動的解釈（Handler）
- **Vorzeichnung（前描画）**: 実行前に Intent の全構造が確定。「実行は忘却である」

### Arrow Effects（分岐禁止）

- ArrowChoice を意図的に実装しない
- 分岐は Cognition（Handler）の責務
- TLA+ でのモデル検証が容易

## モノレポ構成

このリポジトリは spago workspace を使用したモノレポ構成です。

| パッケージ | 説明 |
|------------|------|
| `noema-core` | DSL コア（Intent, Arrow, AVDC 語彙） |
| `noema-retail` | 小売業実装（在庫、チャネルアダプター、Platform） |

## ディレクトリ構造

```
packages/
├── noema-core/                    # DSL コア
│   ├── src/
│   │   ├── Control/Arrow.purs     # Arrow 型クラス
│   │   ├── Noema/
│   │   │   ├── Topos/             # トポス構造（内的）
│   │   │   │   ├── Situs.purs     # 空間座標
│   │   │   │   ├── Nomos.purs     # 法座標
│   │   │   │   └── Presheaf.purs  # ステージング
│   │   │   ├── Horizont/          # 地平線（外的）
│   │   │   │   └── Carrier.purs   # 外部接続の担体
│   │   │   ├── Vorzeichnung/      # 予描図式（Intent, Combinators）
│   │   │   │   └── Vocabulary/    # AVDC 語彙
│   │   │   │       ├── SubjectF.purs
│   │   │   │       ├── ThingF.purs
│   │   │   │       ├── RelationF.purs
│   │   │   │       ├── ContractF.purs
│   │   │   │       └── NoemaF.purs
│   │   │   ├── Cognition/Interpretation.purs
│   │   │   └── Sedimentation/     # Factum, Seal
│   └── spago.yaml
│
└── noema-retail/                  # 小売実装
    ├── src/
    │   ├── Main.purs              # Worker エントリーポイント
    │   ├── Noema/
    │   │   ├── Vorzeichnung/Vocabulary/
    │   │   │   ├── InventoryF.purs
    │   │   │   └── Item.purs           # Retail 固有の Thing 具体化
    │   │   ├── Cognition/
    │   │   │   ├── InventoryInterpretation.purs
    │   │   │   ├── SubjectInterpretation.purs
    │   │   │   ├── ThingInterpretation.purs    # Thing 操作の解釈
    │   │   │   └── StorageInterpretation.purs
    │   ├── Horizont/              # 外界との地平線（Carrier 実装）
    │   │   ├── Channel.purs
    │   │   ├── InventoryCarrier.purs
    │   │   └── Rakuten, Smaregi, Yahoo, Stripe
    │   ├── TlaPlus/               # TLA+ 連携
    │   └── Platform/Cloudflare/   # Cloudflare Workers 実装
    │       ├── Router.purs
    │       ├── InventoryAttractor.purs  # 在庫管理 DO
    │       ├── SubjectAttractor.purs    # 主体管理 DO
    │       └── FFI/               # DurableObject, Request, Response, etc.
    ├── worker.js                  # Cloudflare Workers エントリーポイント
    └── spago.yaml

tlaplus/
└── specs/                          # TLA+ 形式検証
    ├── InventorySimple.tla
    └── InventorySimple.cfg
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
spago build                     # 全パッケージビルド
spago build -p noema-core       # DSL コアのみ
spago build -p noema-retail     # 小売実装のみ

# テスト
spago test                      # 全パッケージテスト
spago test -p noema-core        # Arrow 法則テスト
spago test -p noema-retail      # 小売実装テスト

# TLA+ 検証
cd tlaplus/specs
java -jar ~/tla2tools.jar -config InventorySimple.cfg InventorySimple.tla

# 開発
npm run build                   # ESBuild バンドル
wrangler dev                    # ローカル起動

# デプロイ
wrangler deploy                    # 開発環境
wrangler deploy --env production   # 本番環境
```

## 開発ガイド

- [設計原理](docs/design-principles.md)
- [Topos（内的構造）](packages/noema-core/src/Noema/Topos/README.md)
- [Horizont（外的地平線）](packages/noema-core/src/Noema/Horizont/README.md)
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
