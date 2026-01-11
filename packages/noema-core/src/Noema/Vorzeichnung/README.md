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
- `Situierung.purs`: Intent の状況付け（World への位置づけ）
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
import Noema.Vorzeichnung.Intent (Intent, arrIntent, (>>>))
import Noema.Vorzeichnung.Vocabulary.ThingF (getProperty, getSitus)

-- Thing の属性取得 Intent
propertyIntent :: Intent ThingF Unit PropertyValue
propertyIntent = getProperty (mkThingId "thing-001") (PropertyKey "price")

-- 合成: 属性取得 → 純粋な変換
pipeline :: Intent ThingF Unit Number
pipeline = propertyIntent >>> arrIntent extractNumber
```

## 他のモジュールとの関係

```
Vorzeichnung/
├── Intent.purs ─────────────────► Cognition/Interpretation.purs
│   (意志の構造)                        (忘却による解釈)
│
├── Situierung.purs                   (World への状況付け)
│
└── Vocabulary/
    ├── SubjectF.purs    ─────────► noema-retail/Cognition/SubjectInterpretation.purs
    ├── ThingF.purs      ─────────► noema-retail/Cognition/ThingInterpretation.purs
    ├── RelationF.purs   ─────────► noema-retail/Cognition/RelationInterpretation.purs
    ├── ContractF.purs   ─────────► noema-retail/Cognition/ContractInterpretation.purs
    └── NoemaF.purs      (Coproduct4 - 上記4つの合成)
```

## ThingF スマートコンストラクタ

```purescript
import Noema.Vorzeichnung.Vocabulary.ThingF

-- 属性操作
getProperty :: ThingId -> PropertyKey -> ThingIntent Unit PropertyValue
setProperty :: ThingId -> PropertyKey -> PropertyValue -> ThingIntent Unit SedimentId

-- 位置操作
getSitus :: ThingId -> ThingIntent Unit SubjectId
recordSitusChange :: ThingId -> SitusChange -> ThingIntent Unit SedimentId

-- 時間構造（Husserl の時間意識）
-- Retention（把持）: 過去の Snapshot
getRetention :: ThingId -> Timestamp -> ThingIntent Unit ThingSnapshot
getRetentionRange :: ThingId -> TimeRange -> ThingIntent Unit (Array ThingSnapshot)

-- Primal（原印象）: 現在の状態
getPrimal :: ThingId -> ThingIntent Unit ThingState

-- Protention（予持）: 未来の Pending Intent
registerProtention :: ThingId -> PendingIntent -> ThingIntent Unit ProtentionId
getProtentions :: ThingId -> ThingIntent Unit (Array PendingIntent)
realizeProtention :: ProtentionId -> ThingIntent Unit SedimentId
cancelProtention :: ProtentionId -> ThingIntent Unit SedimentId
```

## ChangeReason（位置変更理由）

noema-core では抽象的な `newtype ChangeReason = ChangeReason Json` として定義。
具体的な理由（Sale, Purchase 等）は noema-retail の `RetailChangeReason` で定義される。

```purescript
-- ドメイン非依存のヘルパー
mkChangeReason :: String -> Maybe String -> Maybe ContractId -> ChangeReason
getReasonType :: ChangeReason -> String
transferReason :: ChangeReason  -- 定義済み定数
```
