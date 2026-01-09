# Vorzeichnung

## 役割

Vorzeichnung（前描画）は Intent（意志）の構造を定義する。
フッサール現象学における「予描」の概念に由来し、まだ認知されていない純粋な意志の形式を表現する。

## 圏論的位置づけ

```
Intent ⊣ Cognition（随伴）
  │
  ├── Vorzeichnung/（左随伴 = 自由関手）
  │   ├── Intent.purs     # Arrow-based Intent
  │   ├── Combinators.purs
  │   └── Vocabulary/     # AVDC 語彙
  │
  └── Cognition/（右随伴 = 忘却関手）
      └── Interpretation.purs
```

| 概念 | 圏論 | 実装 |
|------|------|------|
| **Vorzeichnung** | 自由関手 | このディレクトリ全体 |
| **Intent** | Freer Arrow | `Intent.purs` |
| **Vocabulary** | 操作の関手 f | `Vocabulary/*.purs` |

## 主要コンポーネント

- `Intent.purs`: Arrow-based Intent の定義。Category, Arrow インスタンスを持つが、ArrowChoice は意図的に未実装（分岐禁止）
- `Combinators.purs`: Intent 合成のためのコンビネータ（dup, swap, both, fanout 等）
- `Vocabulary/`: 操作の語彙（SubjectF, ThingF, RelationF, ContractF, NoemaF）

## 設計原則

### Arrow Effects（分岐禁止）

```purescript
-- ArrowChoice は実装しない
-- class Arrow a <= ArrowChoice a where
--   left :: a b c -> a (Either b d) (Either c d)

-- これにより、以下が型レベルで禁止される:
-- if condition then operation1 else operation2
```

分岐は Cognition（Interpretation）層の責務。

### Intent の静的構造

```purescript
-- Intent は実行前に全構造が確定
getStock tid sid >>> arrIntent _.quantity
-- 分岐は含まれない
```

## 使用例

```purescript
import Noema.Vorzeichnung.Intent (Intent, liftEffect, arrIntent, (>>>))
import Noema.Vorzeichnung.Vocabulary.InventoryF (getStock, setStock)

-- 在庫取得 Intent
stockIntent :: Intent InventoryF Unit StockInfo
stockIntent = getStock (ThingId "SKU-001") (mkSubjectId "warehouse-001")

-- 合成
pipeline :: Intent InventoryF Unit Quantity
pipeline = stockIntent >>> arrIntent _.quantity
```

## 他のモジュールとの関係

```
Vorzeichnung/
├── Intent.purs ─────────────────► Cognition/Interpretation.purs
│   (意志の構造)                        (忘却による解釈)
│
└── Vocabulary/
    ├── SubjectF.purs    ─────────► noema-retail/Cognition/SubjectInterpretation.purs
    ├── ThingF.purs
    ├── InventoryF.purs  ─────────► noema-retail/Cognition/InventoryInterpretation.purs
    └── NoemaF.purs      (Coproduct4)
```
