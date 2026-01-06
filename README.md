# Noema Retail

小売業バックエンドを構成可能な DSL。Vorzeichnungsschema（予描図式）として意志を構造化し、実行（忘却）によって事実に崩落させる。

## システム概要

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              販売チャネル                                     │
├─────────────┬─────────────┬─────────────┬─────────────┬─────────────────────┤
│   自社EC    │  楽天市場   │Yahoo!ショッピング│  スマレジ   │    将来拡張         │
│ Astro+Stripe│    RMS      │ ストアクリエイター │    POS     │   (Amazon等)       │
└──────┬──────┴──────┬──────┴──────┬──────┴──────┬──────┴─────────────────────┘
       │ Webhook     │ RMS API     │ Yahoo API   │ スマレジAPI
       ▼             ▼             ▼             ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Noema Gateway (Cloudflare Workers)                       │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  Channel Adapters: Stripe | Rakuten | Yahoo | Smaregi               │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│                                    ▼ Intent (Freer InventoryF)              │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                 InventoryAttractor (Durable Object)                  │   │
│  │                      SQLite: inventory, logs, sync                   │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────┘
```

## 圏論的構造

```
                Intent (Freer RetailF)
                      │
          ┌───────────┼───────────┬───────────┐
          │           │           │           │
          ▼           ▼           ▼           ▼
    ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌───────────┐
    │SubjectF │ │ ThingF  │ │ContextF│ │InventoryF │
    └────┬────┘ └────┬────┘ └────┬────┘ └─────┬─────┘
         │           │           │             │
         ▼           ▼           ▼             ▼
      Subject      Thing      Context      Inventory
        圏          圏          圏           圏
```

### 核心定式

> **プログラムとは、主体が世界に対して投げかける意志を、Vorzeichnungsschema として構造化し、認知（Cognition）による忘却を通じて事実へと崩落させる、対話的運動である。**

> **実行とは忘却である。**

## ディレクトリ構造

```
noema-retail/
├── docs/
│   ├── categorical-model.md       # 圏論的モデル
│   └── inventory-sync-architecture.md  # 在庫連携アーキテクチャ
├── src/
│   ├── core/
│   │   ├── Freer.purs            # Freer モナド
│   │   ├── Coyoneda.purs         # 余米田（自由関手構成）
│   │   └── Coproduct.purs        # 余積（語彙統合）
│   ├── domain/
│   │   ├── Base.purs             # 基本型
│   │   ├── Subject.purs          # 契約主体
│   │   ├── Thing.purs            # 物（多視点）
│   │   ├── Context.purs          # 時空間
│   │   ├── Contract.purs         # 契約
│   │   ├── Inventory.purs        # 在庫
│   │   ├── Retail.purs           # 統合DSL
│   │   └── Flows.purs            # 取引フロー
│   └── adapter/
│       └── Channel.purs          # チャネルアダプター型
├── workers/
│   ├── index.ts                  # Worker エントリーポイント
│   ├── attractors/
│   │   └── InventoryAttractor.ts # 在庫管理 Durable Object
│   └── adapters/
│       ├── SmaregiAdapter.ts     # スマレジ連携
│       ├── RakutenAdapter.ts     # 楽天市場連携
│       ├── YahooAdapter.ts       # Yahoo!ショッピング連携
│       └── StripeAdapter.ts      # Stripe Webhook
└── wrangler.toml                 # Cloudflare Workers 設定
```

## 在庫連携フロー

### 販売イベント（Sale）

```
[チャネル] ─ Webhook/Polling ─> [Adapter] ─ Intent ─> [InventoryAttractor]
                                    │
                                    ▼
                          InventoryEvent.Sale {
                            productId, channel, quantity,
                            orderId, timestamp
                          }
                                    │
                                    ▼
                          [1] 在庫減算
                          [2] ログ記録（イベントソーシング）
                          [3] 他チャネル同期
```

### 同期フロー

```
[在庫変動発生]
      │
      ├──> 楽天: RakutenAdapter.syncFromNoema()
      ├──> Yahoo: YahooAdapter.syncFromNoema()
      ├──> スマレジ: SmaregiAdapter.syncFromNoema()
      └──> 自社EC: (Noema が Single Source of Truth)
```

## API エンドポイント

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/inventory/:productId/:locationId` | GET | 在庫取得 |
| `/api/inventory` | POST | 在庫作成/更新 |
| `/api/inventory/adjust` | POST | 在庫調整 |
| `/api/inventory/reserve` | POST | 在庫予約 |
| `/api/sync/:channel/:productId` | POST | チャネル同期 |
| `/api/sync/all/:productId` | POST | 全チャネル同期 |
| `/api/sync/status/:productId` | GET | 同期状態取得 |
| `/webhook/stripe` | POST | Stripe Webhook |

## セットアップ

### 1. 環境変数設定

```bash
# Stripe
wrangler secret put STRIPE_API_KEY
wrangler secret put STRIPE_WEBHOOK_SECRET

# 楽天市場
wrangler secret put RAKUTEN_SERVICE_SECRET
wrangler secret put RAKUTEN_LICENSE_KEY

# Yahoo!ショッピング
wrangler secret put YAHOO_CLIENT_SECRET
wrangler secret put YAHOO_REFRESH_TOKEN
wrangler secret put YAHOO_PUBLIC_KEY

# スマレジ
wrangler secret put SMAREGI_CLIENT_SECRET
wrangler secret put SMAREGI_ACCESS_TOKEN
```

### 2. デプロイ

```bash
# 開発環境
wrangler dev

# 本番環境
wrangler deploy --env production
```

## 次のステップ

1. **Astro フロントエンド**: 自社EC サイトの構築
2. **Stripe Elements**: 決済フォームの統合
3. **商品マスタ**: ProductAttractor の実装
4. **Nomos 制約**: Lean4 による法的制約の証明
5. **管理画面**: 在庫/注文/同期状態のダッシュボード

## 各チャネルAPI認証情報の更新

| チャネル | 認証方式 | 更新頻度 |
|----------|----------|----------|
| 楽天市場 | serviceSecret + licenseKey | ライセンスキー: 年次 |
| Yahoo!ショッピング | OAuth2 + 公開鍵 | 公開鍵: 年次, トークン: 12時間 |
| スマレジ | OAuth2 | アクセストークン: 定期更新 |
| Stripe | API Key | 必要時 |
