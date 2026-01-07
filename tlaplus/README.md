# TLA+ Specifications

## 役割

Noema DSL の形式的検証基盤。TLA+（Temporal Logic of Actions）を用いて、Intent の正しさを数学的に証明する。

## 圏論的位置づけ

TLA+ 仕様は Intent の意味論を形式化する：

```
Intent (PureScript)  ─────>  TLA+ Specification
        │                          │
        │ runIntent                │ TLC Model Checker
        ▼                          ▼
     Effect              State Space Exploration
```

Arrow-TLA+ 対応：

| Arrow (PureScript) | TLA+ |
|-------------------|------|
| `f >>> g` | F ∘ G（逐次合成） |
| `f *** g` | F ∧ G（並列合成） |
| `arr f` | vars' = f(vars)（純粋変換） |
| `liftEffect op` | Action |

## ディレクトリ構造

```
tlaplus/
├── README.md           # このファイル
├── specs/              # TLA+ 仕様ファイル
│   ├── InventorySimple.tla   # 在庫操作の仕様
│   └── InventorySimple.cfg   # TLC 設定
└── scripts/            # 検証スクリプト
```

## 主要仕様

### InventorySimple.tla

在庫操作の TLA+ 仕様：

```tla
---- MODULE InventorySimple ----
EXTENDS Integers, FiniteSets

CONSTANTS ProductIds, LocationIds, MaxQuantity, Channels

VARIABLES stock, reserved, pendingSync

\* 操作定義
SetStock(pid, lid, qty) == ...
AdjustStock(pid, lid, delta) == ...
ReserveStock(pid, lid, qty) == ...
ReleaseReservation(pid, lid, qty) == ...

\* 不変条件
NonNegativeStock == \A pid \in ProductIds, lid \in LocationIds:
    stock[<<pid, lid>>] >= 0
MaximumStock == \A pid \in ProductIds, lid \in LocationIds:
    stock[<<pid, lid>>] <= MaxQuantity

====
```

## 検証された不変条件

| 不変条件 | 説明 |
|---------|------|
| `NonNegativeStock` | 在庫は常に 0 以上 |
| `ReservationBound` | 予約は常に 0 以上 |
| `MaximumStock` | 在庫は MaxQuantity 以下 |

## 発見されたバグと修正

TLA+ モデル検証により発見された問題：

### Bug 1: ReleaseReservation overflow

```
State 4: stock = 3, reserved = 1 (MaxQuantity = 3)
State 5: ReleaseReservation(1) → stock = 4 > MaxQuantity
```

**修正**: `stock + qty <= MaxQuantity` ガードを追加

### Bug 2: ReserveStock overflow

```
State 3: reserved = 2, stock = 0
State 4: SetStock → stock = 2
State 5: ReserveStock(2) → reserved = 4 > MaxQuantity
```

**修正**: `reserved + qty <= MaxQuantity` ガードを追加

## 使用方法

### TLC でモデル検証

```bash
cd tlaplus/specs
java -jar ~/tla2tools.jar -config InventorySimple.cfg InventorySimple.tla
```

### 期待される出力

```
Model checking completed. No error has been found.
213 states generated, 32 distinct states found, 0 states left on queue.
```

## 設定ファイル（.cfg）

```
CONSTANTS
  ProductIds = {p1}
  LocationIds = {l1}
  MaxQuantity = 3
  Channels = {ch1}

INIT Init
NEXT Next

INVARIANTS
  TypeOK
  NonNegativeStock
  ReservationBound
  MaximumStock
```

## 関連

- [../src/Noema/Vorzeichnung/](../src/Noema/Vorzeichnung/README.md) - Intent 定義
- [../src/Noema/Cognition/](../src/Noema/Cognition/README.md) - Handler 実装（ガード含む）
- [../src/TlaPlus/](../src/TlaPlus/) - TLA+ 連携コード
- [../docs/tla-pipeline.md](../docs/tla-pipeline.md) - TLA+ パイプライン詳細
