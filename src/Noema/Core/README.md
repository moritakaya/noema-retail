# Core

## 役割

Noema DSL の基本型と座標系を定義する。空間座標（Locus）と法座標（World）により、分散システムの位置と文脈を表現する。

## 圏論的位置づけ

- **Locus（空間座標）**: Base 圏の対象を識別
- **World（法座標）**: Fiber 圏の解釈を規定

```
グロタンディーク構成:
  Base 圏: DO のネットワーク（水平射 = RPC）
  Fiber 圏: 各 DO 内の状態空間（垂直射 = Sediment）

DO が眠って起きた時:
  - Locus は同じ
  - World が変わりうる（コードのデプロイ）
```

## 主要コンポーネント

| ファイル | 役割 |
|---------|------|
| `Locus.purs` | 空間座標と識別子（LocusId, SubjectId, ThingId, etc.） |
| `World.purs` | 法座標と Nomos（NomosVersion, World, IntentContext） |

## 識別子の種類

```purescript
-- DO の識別子（空間座標）
newtype LocusId = LocusId String

-- Subject: 意志を持つ主体（DO として実装）
newtype SubjectId = SubjectId LocusId

-- Thing: 意志を持たない物（DO ではない、Guardian に包摂）
newtype ThingId = ThingId String

-- Contract: 契約（DO として実装）
newtype ContractId = ContractId LocusId

-- Relation: 関係
newtype RelationId = RelationId String

-- Sediment: 状態変更の記録（Lamport Clock）
newtype SedimentId = SedimentId Int
```

## 存在論的三層構造

```
Nomos（大域意志）
  法律、商習慣、ビジネスルール
  Sediment の解釈を規定する「法」
        ↓ 規定
Subject（意志を持つ主体）    Thing（意志を持たない物）
  DO として実装              Guardian Subject に包摂
  能動的に Sediment を沈殿   Subject^op → Set として観測
```

## 使用例

```purescript
import Noema.Core.Locus (SubjectId(..), ThingId(..), LocusId(..))
import Noema.Core.World (NomosVersion(..), mkWorld)

-- Subject の作成
seller :: SubjectId
seller = SubjectId (LocusId "seller-001")

-- Thing の作成（Guardian に包摂される）
product :: ThingId
product = ThingId "product-sku-123"

-- World の作成
world :: World
world = mkWorld (NomosVersion "1.0.0") (Timestamp 1704067200000.0)
```

## 関連

- [../Vorzeichnung/](../Vorzeichnung/README.md) - Intent の構造
- [../Cognition/](../Cognition/README.md) - Handler 実装
