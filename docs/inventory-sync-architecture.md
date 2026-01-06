# Noema Retail: 在庫連携アーキテクチャ

## 1. システム構成

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              販売チャネル                                     │
├─────────────┬─────────────┬─────────────┬─────────────┬─────────────────────┤
│   自社EC    │  楽天市場   │Yahoo!ショッピング│  スマレジ   │    将来拡張         │
│ Astro+Stripe│    RMS      │ ストアクリエイター │    POS     │   (Amazon等)       │
└──────┬──────┴──────┬──────┴──────┬──────┴──────┬──────┴─────────────────────┘
       │             │             │             │
       │ Stripe      │ RMS API     │ Yahoo API   │ スマレジAPI
       │ Webhook     │ (在庫API2.0)│ (setStock)  │ (Platform API)
       ▼             ▼             ▼             ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Noema Gateway (Cloudflare Workers)                  │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  Channel Adapter Layer                                               │   │
│  │  ├── StripeAdapter      : Webhook → InventoryEvent                  │   │
│  │  ├── RakutenAdapter     : RMS API ↔ InventoryEvent                  │   │
│  │  ├── YahooAdapter       : Yahoo API ↔ InventoryEvent                │   │
│  │  └── SmaregiAdapter     : Platform API ↔ InventoryEvent             │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│                                    ▼ Intent (Freer InventoryF)              │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                    Noema Core (Durable Objects)                      │   │
│  │                                                                      │   │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐  │   │
│  │  │ InventoryAttractor│  │  ProductAttractor │  │  ChannelAttractor │  │   │
│  │  │ (在庫管理DO)      │  │  (商品マスタDO)   │  │  (チャネル状態DO) │  │   │
│  │  └────────┬─────────┘  └────────┬─────────┘  └────────┬─────────┘  │   │
│  │           │                     │                     │             │   │
│  │           └─────────────────────┴─────────────────────┘             │   │
│  │                                 │                                    │   │
│  │                     ┌───────────▼───────────┐                       │   │
│  │                     │   SQLite (DO Storage)  │                       │   │
│  │                     │   ├── inventory        │                       │   │
│  │                     │   ├── inventory_log    │                       │   │
│  │                     │   ├── channel_sync     │                       │   │
│  │                     │   └── product_master   │                       │   │
│  │                     └───────────────────────┘                       │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────┘
```

## 2. 圏論的モデル

### 2.1 在庫の多視点表現

在庫は Thing 圏の特殊化であり、複数のチャネルから「見られる」。

$$\text{Inventory} : \mathbf{Channel}^{op} \to \mathbf{Set}$$

各チャネル $c$ に対して $\text{Inventory}(c)$ は「チャネル $c$ から見た在庫数」を返す。

```
y(在庫) = { 楽天から見た在庫, Yahoo!から見た在庫, スマレジから見た在庫, 自社ECから見た在庫 }
```

### 2.2 在庫イベントの圏

$$\mathbf{InventoryEvent} = (\text{Ob}, \text{Hom}, \circ, \text{id})$$

- **対象**: 在庫状態 $(product, channel, quantity, timestamp)$
- **射**: 在庫変動イベント（販売、入荷、移動、調整）

### 2.3 同期の整合性

各チャネルへの在庫反映は「忘却」の一種：

$$\text{Sync}_c : \text{Inventory}_{Noema} \to \text{Inventory}_c$$

全チャネルへの同期は積関手：

$$\text{SyncAll} = \prod_{c \in \text{Channel}} \text{Sync}_c$$

## 3. データモデル

### 3.1 商品マスタ（Product）

```sql
CREATE TABLE product (
    id TEXT PRIMARY KEY,                    -- Noema内部ID（UUID）
    sku TEXT NOT NULL UNIQUE,               -- 統一SKU
    name TEXT NOT NULL,
    description TEXT,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL
);

-- チャネル別商品マッピング
CREATE TABLE product_channel (
    product_id TEXT NOT NULL REFERENCES product(id),
    channel TEXT NOT NULL,                  -- 'rakuten', 'yahoo', 'smaregi', 'self_ec'
    external_id TEXT NOT NULL,              -- チャネル側の商品ID
    external_sku TEXT,                      -- チャネル側のSKU
    sync_enabled BOOLEAN DEFAULT TRUE,
    last_synced_at INTEGER,
    PRIMARY KEY (product_id, channel)
);
```

### 3.2 在庫（Inventory）

```sql
-- 統合在庫（Single Source of Truth）
CREATE TABLE inventory (
    id TEXT PRIMARY KEY,
    product_id TEXT NOT NULL REFERENCES product(id),
    location_id TEXT NOT NULL,              -- 'warehouse', 'store_001', etc.
    quantity INTEGER NOT NULL DEFAULT 0,
    reserved INTEGER NOT NULL DEFAULT 0,    -- 予約済み（注文確定待ち）
    available INTEGER GENERATED ALWAYS AS (quantity - reserved) STORED,
    updated_at INTEGER NOT NULL
);

-- 在庫変動ログ（イベントソーシング）
CREATE TABLE inventory_log (
    id TEXT PRIMARY KEY,
    inventory_id TEXT NOT NULL REFERENCES inventory(id),
    event_type TEXT NOT NULL,               -- 'sale', 'purchase', 'adjust', 'transfer', 'reserve', 'release'
    channel TEXT NOT NULL,                  -- イベント発生元チャネル
    quantity_delta INTEGER NOT NULL,        -- 変動量（負は減少）
    reference_id TEXT,                      -- 注文ID等の参照
    created_at INTEGER NOT NULL,
    metadata TEXT                           -- JSON形式の追加情報
);

-- チャネル別同期状態
CREATE TABLE channel_sync (
    product_id TEXT NOT NULL REFERENCES product(id),
    channel TEXT NOT NULL,
    local_quantity INTEGER NOT NULL,        -- Noema側の認識
    remote_quantity INTEGER,                -- チャネル側の認識（最終取得時）
    sync_status TEXT NOT NULL,              -- 'synced', 'pending', 'error', 'conflict'
    last_sync_at INTEGER,
    last_error TEXT,
    PRIMARY KEY (product_id, channel)
);
```

## 4. 在庫イベントフロー

### 4.1 販売イベント（Sale）

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
                          [1] 在庫減算（inventory.quantity -= delta）
                          [2] ログ記録（inventory_log に追加）
                          [3] 他チャネル同期（SyncAll を発火）
```

### 4.2 同期フロー

```
             ┌──────────────────────────────────────────────┐
             │         InventoryAttractor                   │
             │                                              │
             │  [在庫変動発生]                               │
             │        │                                     │
             │        ▼                                     │
             │  [全チャネルに対してループ]                    │
             │        │                                     │
             │        ├──> 楽天: RakutenAdapter.sync()      │
             │        ├──> Yahoo: YahooAdapter.sync()       │
             │        ├──> スマレジ: SmaregiAdapter.sync()  │
             │        └──> 自社EC: SelfECAdapter.sync()     │
             │                                              │
             │  [sync_statusを更新]                         │
             └──────────────────────────────────────────────┘
```

## 5. 各チャネルAPI仕様

### 5.1 楽天市場（RMS）

| 項目 | 内容 |
|------|------|
| 認証 | serviceSecret + licenseKey（年次更新） |
| 在庫取得 | `inventories.bulk.get`（在庫API 2.0） |
| 在庫更新 | `inventories.bulk.upsert`（在庫API 2.0） |
| 注文取得 | `rpay.order.searchOrder`（楽天ペイ受注API） |
| レート制限 | 要確認（API設定画面） |

### 5.2 Yahoo!ショッピング

| 項目 | 内容 |
|------|------|
| 認証 | OAuth2（リフレッシュトークン + 公開鍵） |
| 在庫取得 | `GET /ShoppingWebService/V1/getStock` |
| 在庫更新 | `POST /ShoppingWebService/V1/setStock` |
| 注文取得 | 注文API（要利用申請） |
| レート制限 | 1リクエスト/秒 |

### 5.3 スマレジ

| 項目 | 内容 |
|------|------|
| 認証 | OAuth2（スマレジプラットフォームAPI） |
| 在庫取得 | `GET /pos/stocks` |
| 在庫更新 | `POST /pos/stocks`（出荷登録で在庫減） |
| 取引取得 | `GET /pos/transactions` |
| プラン | リテールビジネスプランで在庫API利用可能 |

### 5.4 自社EC（Stripe）

| 項目 | 内容 |
|------|------|
| 認証 | Stripe API Key + Webhook Secret |
| 在庫管理 | Noema側で管理（Stripeは決済のみ） |
| 注文通知 | `checkout.session.completed` Webhook |

## 6. Noema DSL 拡張

### 6.1 在庫操作（InventoryF）

```purescript
data InventoryF next
  -- 在庫操作
  = GetStock ProductId LocationId (Quantity -> next)
  | AdjustStock ProductId LocationId QuantityDelta Reason (Inventory -> next)
  | ReserveStock ProductId LocationId Quantity OrderRef (ReservationId -> next)
  | ReleaseReservation ReservationId (Unit -> next)
  -- チャネル同期
  | SyncToChannel ProductId Channel (SyncResult -> next)
  | SyncFromChannel ProductId Channel (SyncResult -> next)
  | SyncAll ProductId (Array SyncResult -> next)
  -- クエリ
  | GetInventoryLog ProductId TimeRange (Array InventoryLogEntry -> next)
  | GetSyncStatus ProductId (Array ChannelSyncStatus -> next)
```

### 6.2 統合語彙の拡張

```purescript
-- RetailF に InventoryF を追加
type RetailF = Coproduct4 SubjectF ThingF ContextF InventoryF
```

## 7. 実装優先順位

### Phase 1: 基盤（Week 1-2）

1. InventoryAttractor の実装
2. SQLite スキーマの作成
3. 基本的な在庫CRUD操作

### Phase 2: チャネルアダプター（Week 3-4）

1. SmaregiAdapter（最も重要：実店舗連携）
2. RakutenAdapter
3. YahooAdapter
4. StripeAdapter（Webhook受信）

### Phase 3: 同期ロジック（Week 5-6）

1. イベント駆動同期
2. 定期ポーリング（フォールバック）
3. コンフリクト解決ロジック

### Phase 4: 自社EC（Week 7-8）

1. Astro フロントエンド
2. Stripe Elements 決済
3. Noema API 連携

## 8. コンフリクト解決

### 8.1 楽観的ロック

```
[チャネルA] ──在庫10─→ [Noema] ←─在庫10─── [チャネルB]
                │
         [販売イベント: -1]
                │
                ▼
[チャネルA] ←─在庫9──→ [Noema] ──在庫9──→ [チャネルB]
```

### 8.2 同時更新の検出

```sql
-- channel_sync.remote_quantity と実際の取得値を比較
-- 乖離があればコンフリクトとして検出
```

### 8.3 解決戦略

1. **Noema優先**: Noemaの在庫を正として各チャネルに上書き
2. **最新優先**: timestamp が最新のイベントを採用
3. **手動解決**: 大きな乖離は管理者に通知

## 9. 監視とアラート

- 同期失敗の検出
- 在庫乖離の検出
- API レート制限の監視
- 在庫切れアラート
