# Vocabulary (noema-retail)

## 役割

noema-retail の Vocabulary は2つの役割を持つ：

1. **ドメイン具体化**: noema-core の抽象型を小売ドメインで具体化
2. **インフラ語彙**: HTTP、ストレージ等のインフラ操作を定義

## 圏論的位置づけ

```
noema-core（抽象）           noema-retail（具体）
    │                              │
    ▼ A-algebra の解釈             ▼
RelationKind ──────────────► RetailRelationKind
ChangeReason ──────────────► RetailChangeReason
    ...                            ...
```

noema-retail の Retail* 型は noema-core の抽象型に対する **A-algebra の解釈** を提供する。

## 主要コンポーネント

### ドメイン具体化（Retail* 型）

| ファイル | noema-core の抽象型 | 小売固有の具体化 |
|----------|---------------------|------------------|
| `RetailRelationKind.purs` | RelationKind (Json) | Owns, Reserves, ActsFor 等 19種 |
| `RetailChangeReason.purs` | ChangeReason (Json) | Sale, Purchase, Return 等 |
| `RetailChangeType.purs` | ChangeType (String) | PriceChanged, AvailabilityChanged 等 |
| `RetailSecurityType.purs` | SecurityType (String) | Pledge, Lien, Mortgage 等（日本民法） |
| `RetailAgencyScope.purs` | AgencyScope (String) | GeneralAgency, SpecificAgency 等 |

### ドメイン実装

| ファイル | 役割 |
|----------|------|
| `Item.purs` | Thing の小売実装（商品）。ItemEvent, ItemState を定義 |
| `Constructors.purs` | InventoryF 操作のスマートコンストラクタ |

### インフラ語彙

| ファイル | 役割 |
|----------|------|
| `InventoryF.purs` | 在庫操作（getStock, reserve, commit 等） |
| `HttpF.purs` | HTTP リクエスト/レスポンス操作 |
| `StorageF.purs` | Durable Object ストレージ操作 |

## 変換パターン

各 Retail* 型は双方向変換関数を提供：

```purescript
-- RetailRelationKind.purs
toRelationKind :: RetailRelationKind -> RelationKind
fromRelationKind :: RelationKind -> Maybe RetailRelationKind

-- 使用例
import Noema.Vorzeichnung.Vocabulary.RetailRelationKind

let abstractKind = toRelationKind Owns
-- => RelationKind {"type":"owns","category":"rights","subtype":null}

let maybeRetail = fromRelationKind abstractKind
-- => Just Owns
```

## RetailRelationKind 一覧

| カテゴリ | 関係種別 | 説明 |
|---------|---------|------|
| rights | Owns, Possesses, Claims, Secures, SharedBy | 権利関係 |
| temporal | Reserves, Commits, Intends | 引当関係 |
| transitive | Transports, Consigns | 移動関係 |
| structural | ComposedOf, BundledWith, Substitutes | 構造関係 |
| cognitive | Observes, Tracks | 観測関係 |
| performative | ActsFor | 代理関係 |
| negative | Restricts | 制限関係 |

## RetailSecurityType（日本民法）

| 型 | 法的根拠 | 説明 |
|---|---------|------|
| Pledge | 民法342条〜 | 質権 |
| Lien | 民法295条〜 | 留置権 |
| Mortgage | 民法369条〜 | 抵当権 |
| SecurityInterest | 判例法理 | 譲渡担保 |
| RetentionOfTitle | 商取引慣行 | 所有権留保 |

## 使用例

```purescript
import Noema.Vorzeichnung.Vocabulary.RetailRelationKind (RetailRelationKind(..), toRelationKind)
import Noema.Vorzeichnung.Vocabulary.RetailChangeReason (RetailChangeReason(..), toChangeReason)
import Noema.Vorzeichnung.Vocabulary.InventoryF (reserve, commit)

-- 在庫引当
reserveIntent :: InventoryIntent Unit ReservationId
reserveIntent = reserve
  { thingId: mkThingId "SKU-001"
  , quantity: mkQuantity 5
  , holderId: mkSubjectId "warehouse-001"
  , reserverId: mkSubjectId "customer-001"
  , expiresAt: Just futureTimestamp
  }

-- 関係を抽象型に変換して使用
let ownsKind = toRelationKind Owns
```

## 他のモジュールとの関係

```
noema-core/Vocabulary/           noema-retail/Vocabulary/
├── RelationF.purs ◄──────────── RetailRelationKind.purs
├── ThingF.purs    ◄──────────── RetailChangeReason.purs
│                                Item.purs
│
noema-retail/Cognition/
├── InventoryInterpretation.purs ◄── InventoryF.purs
├── StorageInterpretation.purs   ◄── StorageF.purs
└── ThingInterpretation.purs     ◄── Item.purs
```
