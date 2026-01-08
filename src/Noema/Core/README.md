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
-- 注: 旧設計の LocationId は SubjectId に統合された
newtype SubjectId = SubjectId LocusId

-- Thing: 意志を持たない物（DO ではない、Guardian に包摂）
newtype ThingId = ThingId String

-- Contract: 契約（DO として実装）
newtype ContractId = ContractId LocusId

-- Relation: 関係
newtype RelationId = RelationId String

-- Sediment: 状態変更の記録（Lamport Clock）
newtype SedimentId = SedimentId Int

-- Quantity: 数量（非負整数）
newtype Quantity = Quantity Int

-- QuantityDelta: 数量変化（正負あり）
newtype QuantityDelta = QuantityDelta Int
```

## 設計変更: LocationId → SubjectId

旧設計では `LocationId`（倉庫、店舗）が在庫の位置を表していた。
新設計では `SubjectId`（Guardian）が Thing を包摂し、
その Subject の位置が Thing の位置を決定する。

これにより：
- 型の重複が解消された
- AVDC 構造との整合性が向上した
- Thing は常に Guardian Subject に包摂されるという設計が明確になった

### 変更一覧

| 項目 | 旧 | 新 |
|------|-----|-----|
| 型名 | `LocationId` | `SubjectId` |
| フィールド | `locationId` | `subjectId` |
| DB カラム | `location_id` | `subject_id` |
| JSON キー | `locationId` | `subjectId` |

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
