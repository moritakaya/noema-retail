# Cognition

## 役割

Cognition（認知）は Intent（意志）を Factum（事実）へ解釈する。
随伴 Intent ⊣ Cognition における右随伴（忘却関手）として機能する。

> **実行とは忘却である。**

## 圏論的位置づけ

```
Intent ⊣ Cognition（随伴）
  │
  ├── Vorzeichnung/（左随伴 = 自由関手）
  │   └── Intent.purs
  │
  └── Cognition/（右随伴 = 忘却関手）
      └── Interpretation.purs
```

| 概念 | 圏論 | 実装 |
|------|------|------|
| **Cognition** | 忘却関手 | このディレクトリ |
| **Interpretation** | 自然変換 f ~> Factum | `Interpretation.purs` |
| **A-algebra homomorphism** | 構造を保存する準同型 | 各 Interpretation 実装 |

## 主要コンポーネント

- `Interpretation.purs`: Interpretation 型と runInterpretation 関数

## 設計原則

### Interpretation = A-algebra homomorphism

```purescript
-- 自然変換として定義
type Interpretation f = forall x. f x -> Factum x

-- Intent を実行
runInterpretation :: Interpretation f -> Intent f a b -> a -> Factum b
```

### 分岐は Interpretation の責務

Intent 層では分岐禁止（ArrowChoice なし）。
分岐が必要な場合は Interpretation 層で処理する。

```purescript
-- Intent: 分岐なし、線形
checkStock :: Intent InventoryF Unit StockInfo
checkStock = getStock thingId subjectId

-- Interpretation: 分岐を含む解釈
interpretWithValidation :: InventoryF ~> Factum
interpretWithValidation (GetStock tid sid k) = do
  info <- getStockFromDB tid sid
  -- 分岐は Interpretation 層で行う
  if info.available > Quantity 0
    then pure (k info)
    else throwError (error "Out of stock")
```

## 使用例

以下は noema-retail での具体的な使用例：

```purescript
import Noema.Cognition.Interpretation (Interpretation, runInterpretation)
import Noema.Sedimentation.Factum (Factum, collapse)

-- Interpretation を定義
interpretInventoryF :: InventoryEnv -> Interpretation InventoryF
interpretInventoryF env = case _ of
  GetStock tid sid k -> do
    result <- queryDB env tid sid
    pure (k result)
  SetStock tid sid qty next -> do
    insertDB env tid sid qty
    pure next

-- Intent を実行
result :: Factum StockInfo
result = runInterpretation (interpretInventoryF env) stockIntent unit

-- Effect へ崩落（エントリーポイントで）
effect :: Effect StockInfo
effect = collapse result
```

## 他のモジュールとの関係

```
Vorzeichnung/Intent.purs
        │
        ↓ runInterpretation
Cognition/Interpretation.purs
        │
        ↓ Factum
Sedimentation/Factum.purs
        │
        ↓ collapse
Effect（外界への崩落）
```

## noema-retail での実装

noema-core では Interpretation の型と実行関数のみを定義。
具体的な Interpretation 実装は noema-retail で提供：

### AVDC 語彙の Interpretation

| ファイル | 語彙 | 説明 |
|----------|------|------|
| `SubjectInterpretation.purs` | SubjectF | 主体操作を SQLite へ解釈 |
| `ThingInterpretation.purs` | ThingF | 物操作を SQLite へ解釈（時間構造含む） |
| `RelationInterpretation.purs` | RelationF | 関係操作を SQLite へ解釈 |
| `ContractInterpretation.purs` | ContractF | 契約操作を SQLite へ解釈 |
| `NoemaInterpretation.purs` | NoemaF | 4語彙を統合（Coproduct4） |

### インフラ語彙の Interpretation

| ファイル | 語彙 | 説明 |
|----------|------|------|
| `InventoryInterpretation.purs` | InventoryF | 在庫操作を SQLite へ解釈 |
| `StorageInterpretation.purs` | StorageF | 汎用ストレージ操作 |

### ThingInterpretation の時間構造

```purescript
-- Husserl の内的時間意識に基づく三層構造
-- Retention（把持）: 過去の Snapshot を取得
getRetention :: ThingId -> Timestamp -> ThingIntent Unit ThingSnapshot

-- Primal（原印象）: 現在の状態を取得
getPrimal :: ThingId -> ThingIntent Unit ThingState

-- Protention（予持）: 未来の Pending Intent を管理
registerProtention :: ThingId -> PendingIntent -> ThingIntent Unit ProtentionId
```
