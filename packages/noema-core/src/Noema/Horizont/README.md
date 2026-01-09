# Horizont

## 役割

Horizont（地平線）は Intent（意志）が外界と接触する境界を定義する。
フッサール現象学における「地平線」の概念に由来し、意識の対象を取り巻く潜在的経験の場を表現する。

## 圏論的位置づけ

```
Horizont（外的前層）Channel^op → Set
    ↓ Carrier（担体）
External System（外部システム）
```

| 概念 | 圏論 | 実装 |
|------|------|------|
| **Horizont** | 外的前層 Channel^op → Set | このディレクトリ全体 |
| **Carrier** | A-algebra の carrier（台集合） | 外部接続の基底型クラス |
| **Channel** | 基底圏の対象 | 外部システム識別子 |

## 主要コンポーネント

- `Carrier.purs`: 外部接続を担う基底型クラス

## 現象学的基盤

### Horizont（地平線）

フッサール現象学において、地平線は：
- 意識の対象を取り巻く潜在的経験の場
- 今は主題的に捉えられていないが、常に「そこにある」背景
- 意識の中心から見た境界

Noema において、Horizont は：
- Intent（意志）が外界と接触する境界
- 内的構造（Topos）と外的世界の間の地平線
- 同期操作を通じてのみアクセス可能な潜在的領域

### Carrier（担体）

代数的構造における carrier（台集合）に由来する。
A-algebra において carrier は代数が作用する対象であり、
Noema において Carrier は外部データを「担う」構造である。

## Topos との対称性

```
┌─────────────────────────────────────────────────────────────┐
│                      Noema 圏                               │
│                                                             │
│  Topos（内的）           ↔           Horizont（外的）       │
│  ├── Situs（空間座標）               ├── Carrier（担体）    │
│  ├── Nomos（法座標）                 └── Channel（基底圏）  │
│  └── Presheaf（内的前層）                                   │
│      Set^{Subject^op}                Set^{Channel^op}       │
│                                                             │
│  Vorzeichnung ⊣ Cognition                                   │
│  （自由関手）   （忘却関手）                                 │
│                                                             │
│  Sedimentation                                              │
│  （層化関手）                                                │
└─────────────────────────────────────────────────────────────┘
```

- **Topos**: 内的論理空間（Subject ネットワーク上の presheaf）
- **Horizont**: 外的地平線（Channel 上の presheaf）

両者は対称的な presheaf 構造を持つが、基底圏が異なる。

## 使用例

```purescript
import Noema.Horizont.Carrier (class Carrier, CarrierError, carrierName, healthCheck)

-- Carrier 型クラスを実装
instance Carrier MyAdapter where
  carrierName _ = "MyExternalSystem"
  healthCheck adapter = do
    -- 外部システムへの接続確認
    pure $ Right unit

-- エラーハンドリング
case result of
  Left (NetworkError msg) -> -- ネットワークエラー
  Left (AuthenticationError msg) -> -- 認証エラー
  Right value -> -- 成功
```

## 他のモジュールとの関係

```
Horizont/
└── Carrier.purs ──────────────────────► noema-retail/Horizont/
                                              │
                                              ├── InventoryCarrier.purs
                                              │   (Carrier を継承)
                                              │
                                              ├── Rakuten.purs
                                              ├── Smaregi.purs
                                              ├── Yahoo.purs
                                              └── Stripe.purs
                                                  (具体実装)
```
