# Claude Code タスク: TLA+ ガードの実装反映

## 背景

TLA+ モデルチェックで以下の2つのバグを発見した：

### バグ1: ReleaseReservation が stock 上限を未チェック
```
State 4: stock = 3, reserved = 1 (MaxQuantity = 3)
State 5: ReleaseReservation(1) → stock = 3 + 1 = 4 > MaxQuantity ❌
```

### バグ2: ReserveStock が reserved 上限を未チェック
```
State 3: reserved = 2, stock = 0
State 4: SetStock → stock = 2, reserved = 2
State 5: ReserveStock(2) → reserved = 2 + 2 = 4 > MaxQuantity ❌
```

## タスク

### 1. TLA+ 仕様ファイルを更新

`tlaplus/specs/InventorySimple.tla` を最新の修正済み版に更新。

修正ポイント：
- `ReserveStock`: `reserved[<<pid, lid>>] + qty <= MaxQuantity` ガード追加
- `ReleaseReservation`: `stock[<<pid, lid>>] + qty <= MaxQuantity` ガード追加

### 2. Handler に TLA+ ガードを反映

`src/Noema/Vorzeichnung/Handler/InventoryHandler.purs` または該当する Handler ファイルに、以下のガードを追加：

```purescript
-- ReserveStock: reserved が上限を超えないことをチェック
handleReserveStock tid lid qty = do
  info <- getStockInfo tid lid
  let newReserved = unwrap info.reserved + unwrap qty
  if unwrap info.available >= unwrap qty && newReserved <= maxQuantity
    then do
      -- 予約実行
      pure true
    else pure false

-- ReleaseReservation: stock が上限を超えないことをチェック  
handleReleaseReservation tid lid qty = do
  info <- getStockInfo tid lid
  let newStock = unwrap info.quantity + unwrap qty
  if newStock <= maxQuantity
    then do
      -- 解放実行
      pure unit
    else throwError StockOverflow
```

### 3. Git コミット

```bash
git add tlaplus/ src/
git commit -m "feat(tla+): Add TLA+ model checking pipeline and fix Handler guards

- Add TLA+ specification for inventory operations (InventorySimple.tla)
- Add TLC configuration (InventorySimple.cfg)
- Fix ReserveStock: check reserved + qty <= MaxQuantity
- Fix ReleaseReservation: check stock + qty <= MaxQuantity

Bugs discovered by TLA+ model checking:
1. ReleaseReservation could overflow stock beyond MaxQuantity
2. ReserveStock could overflow reserved beyond MaxQuantity

Arrow-TLA+ correspondence:
  f >>> g  ↔  F ∘ G (sequential)
  f *** g  ↔  F ∧ G (parallel)
  arr f    ↔  vars' = f(vars)"

git push origin main
```

## ファイル構造

```
noema-retail/
├── tlaplus/
│   └── specs/
│       ├── InventorySimple.tla   # 修正済みTLA+仕様
│       └── InventorySimple.cfg   # TLC設定
├── src/Noema/Vorzeichnung/
│   ├── Intent.purs               # Arrow-based Intent
│   └── Vocabulary/
│       └── InventoryF.purs       # 在庫語彙
└── .github/workflows/
    └── tla-check.yml             # GitHub Actions (optional)
```

## 検証コマンド

```bash
# TLA+ 検証
cd tlaplus/specs
java -jar ~/tla2tools.jar -config InventorySimple.cfg InventorySimple.tla

# PureScript ビルド
spago build

# テスト
spago test
```

## 期待される TLC 出力

```
Model checking completed. No error has been found.
213 states generated, 32 distinct states found, 0 states left on queue.
```
