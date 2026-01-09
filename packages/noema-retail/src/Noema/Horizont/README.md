# Horizont（小売実装）

## 役割

Horizont（地平線）は Intent（意志）が外界と接触する境界を定義する。
noema-core の `Horizont/Carrier` を継承し、小売ドメイン固有のチャネル（楽天、スマレジ等）への接続を実装する。

## 圏論的位置づけ

```
Horizont（外的前層）Channel^op → Set
    ↓ InventoryCarrier（Carrier 拡張）
External System（外部システム）
```

| 概念 | 圏論 | 実装 |
|------|------|------|
| **Horizont** | 外的前層 Channel^op → Set | このディレクトリ全体 |
| **Carrier** | A-algebra の carrier（台集合） | noema-core で定義 |
| **InventoryCarrier** | Carrier の在庫ドメイン拡張 | `InventoryCarrier.purs` |
| **Channel** | 基底圏の対象 | `Channel.purs` |

## 主要コンポーネント

- `Channel.purs`: 小売チャネルの列挙型（Own, Smaregi, Rakuten, Yahoo, Stripe）
- `InventoryCarrier.purs`: 在庫操作用 Carrier 型クラス（noema-core の Carrier を継承）
- `Rakuten.purs`: 楽天市場 RMS API との連携
- `Smaregi.purs`: スマレジ POS API との連携
- `Yahoo.purs`: Yahoo!ショッピング API との連携
- `Stripe.purs`: Stripe 決済 API との連携（Webhook 経由）

## noema-core との関係

```
noema-core                    noema-retail
────────────────────────────────────────────────
Horizont/                     Horizont/
├── Carrier.purs              ├── Channel.purs        # 基底圏の対象
│   (基底型クラス)             ├── InventoryCarrier.purs  # Carrier 拡張
│                             ├── Rakuten.purs        # 具体実装
│                             ├── Smaregi.purs
│                             ├── Yahoo.purs
│                             └── Stripe.purs
```

継承関係:
```
Carrier (noema-core)
    ↑ 継承
InventoryCarrier (noema-retail)
    ↑ 実装
RakutenAdapter, SmaregiAdapter, ... (noema-retail)
```

## 使用例

```purescript
import Noema.Horizont.Channel (Channel(..))
import Noema.Horizont.InventoryCarrier (class InventoryCarrier, getStock, setStock)
import Noema.Horizont.Rakuten (RakutenAdapter, mkRakutenAdapter)
import Noema.Horizont.Carrier (class Carrier, CarrierError(..))

-- Carrier の作成
rakuten :: RakutenAdapter
rakuten = mkRakutenAdapter
  { shopUrl: "https://www.rakuten.co.jp/myshop/"
  , serviceSecret: "..."
  , licenseKey: "..."
  , licenseExpiry: 1735689600000.0
  }

-- InventoryCarrier メソッドの使用
result <- getStock rakuten (ThingId "SKU-001")
case result of
  Left (ApiError code msg) -> -- API エラー
  Left (AuthenticationError msg) -> -- 認証エラー
  Right stockInfo -> -- 成功
```

## チャネル一覧

| Channel | 説明 | API |
|---------|------|-----|
| `Own` | 自社（Noema が Single Source of Truth） | - |
| `Smaregi` | スマレジ POS | Bearer token |
| `Rakuten` | 楽天市場 RMS | ESA 認証 |
| `Yahoo` | Yahoo!ショッピング | OAuth2 |
| `Stripe` | Stripe 決済 | API Key + Webhook |

## Topos との対称性

```
┌─────────────────────────────────────────────────────────────┐
│                      Noema 圏                               │
│                                                             │
│  Topos（内的）           ↔           Horizont（外的）       │
│  ├── Situs（空間座標）               ├── Carrier（担体）    │
│  ├── Nomos（法座標）                 ├── Channel（基底圏）  │
│  └── Presheaf（内的前層）            └── InventoryCarrier   │
│      Set^{Subject^op}                    Set^{Channel^op}   │
│                                                             │
│  Vorzeichnung ⊣ Cognition                                   │
│  （自由関手）   （忘却関手）                                 │
└─────────────────────────────────────────────────────────────┘
```

- **Topos**: 内的論理空間（Subject ネットワーク上の presheaf）
- **Horizont**: 外的地平線（Channel 上の presheaf）

両者は対称的な presheaf 構造を持つが、基底圏が異なる。
