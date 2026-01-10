# Intent ↔ TLA+ 検証パイプライン

## 概要

Noema の Intent（Arrow Effects）と TLA+ 仕様の間に圏論的対応を構築し、
形式検証を実現するパイプライン。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Noema Verification Pipeline                       │
│                                                                      │
│  ┌──────────────┐         ┌──────────────┐         ┌──────────────┐ │
│  │   Intent     │ ─────▶ │  TLA+ Spec   │ ─────▶ │   TLC        │ │
│  │ (PureScript) │ extract│   (.tla)     │  check │ Model Check  │ │
│  └──────────────┘         └──────────────┘         └──────────────┘ │
│         ↑                        │                        │         │
│         │                        ▼                        ▼         │
│         │                 ┌──────────────┐         ┌──────────────┐ │
│         │                 │  Invariants  │         │Counterexample│ │
│         │                 │  Liveness    │         │   Trace      │ │
│         │                 └──────────────┘         └──────────────┘ │
│         │                                                 │         │
│         └────────────────── feedback ─────────────────────┘         │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

## 圏論的基盤

### Intent と TLA+ Action の対応

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Functor: Intent → TLA+                           │
│                                                                      │
│  PureScript (Arrow)              TLA+ (Action)                       │
│  ─────────────────────────────   ────────────────────────────────   │
│  Intent f a b                    Action(vars, vars')                 │
│                                                                      │
│  id :: Intent f a a              UNCHANGED vars                      │
│  f >>> g                         F ∘ G (sequential composition)      │
│  f *** g                         F ∧ G (parallel composition)        │
│  arr f                           vars' = f(vars)                     │
│  liftEffect op                   Op(vars, vars')                     │
│                                                                      │
│  ArrowChoice なし                Non-determinism は Next で表現      │
└─────────────────────────────────────────────────────────────────────┘
```

### 関手性の保証

```
Φ : Arrow(Intent) → Category(TLA+)

Φ(id) = UNCHANGED
Φ(f >>> g) = Φ(f) ∘ Φ(g)
Φ(arr f) = λs. f(s)
Φ(first f) = λ(s, t). (Φ(f)(s), t)
```

この対応が関手であることは、Arrow 法則から導かれる。

## ディレクトリ構造

```
noema-retail/
├── tlaplus/
│   ├── specs/                      # TLA+ 仕様
│   │   ├── Inventory.tla           # 在庫モジュール
│   │   └── Inventory.cfg           # TLC 設定
│   │
│   ├── scripts/                    # ユーティリティ
│   │   └── run-tlc.sh              # ローカル実行
│   │
│   └── tools/                      # TLA+ ツール（自動DL）
│       └── tla2tools.jar
│
├── src/Noema/
│   └── Vorzeichnung/
│       ├── Intent.purs             # Arrow-based Intent
│       └── Vocabulary/
│           └── InventoryF.purs     # 在庫語彙
│
└── .github/workflows/
    └── tla-check.yml               # CI/CD 統合
```

## 使用方法

### ローカル実行

```bash
# TLC を実行
./tlaplus/scripts/run-tlc.sh

# 特定のスペックを実行
./tlaplus/scripts/run-tlc.sh Inventory
```

### CI/CD

GitHub Actions が以下のタイミングで自動実行:
- `main` ブランチへのプッシュ（tlaplus/** が変更された場合）
- プルリクエスト（tlaplus/** が変更された場合）
- 手動トリガー

## 検証される性質

### 安全性（Safety）

| 性質 | TLA+ | 説明 |
|------|------|------|
| NonNegativeStock | `∀ pid, lid: stock[pid, lid] >= 0` | 在庫は非負 |
| ReservationBound | `∀ pid, lid: reserved[pid, lid] >= 0` | 予約は非負 |
| MaximumStock | `∀ pid, lid: stock[pid, lid] <= MaxQuantity` | 在庫は上限以下 |
| TypeOK | 型不変条件 | 型整合性 |

### 活性（Liveness）

| 性質 | TLA+ | 説明 |
|------|------|------|
| SyncEventuallyCompletes | `pendingSync # {} ~> pendingSync = {}` | 同期は最終的に完了 |
| ReservationEventuallyResolved | `reserved > 0 ~> reserved = 0` | 予約は最終的に解決 |

## Intent → TLA+ マッピング例

### PureScript Intent

```purescript
-- 販売Intent: 在庫を1減らす
-- 注: SubjectId は Subject（倉庫、店舗など）を識別。Thing は Subject に包摂される
saleIntent :: ThingId -> SubjectId -> Intent' InventoryF Unit Quantity
saleIntent tid sid =
  getStock tid sid
  >>> arr _.quantity
  >>> arr (\q -> (tid, sid, QuantityDelta (-1)))
  >>> adjustStock'
```

### TLA+ Action

```tla
\* Sale: getStock >>> adjustStock(-1)
Sale(pid, lid) ==
  /\ stock[<<pid, lid>>] > 0
  /\ stock' = [stock EXCEPT ![<<pid, lid>>] = @ - 1]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
  /\ UNCHANGED reserved
```

## 反例からのフィードバック

TLC が反例を発見した場合:

```
State 1: stock = [<<"SKU-001", "LOC-001">> |-> 1]
State 2: stock = [<<"SKU-001", "LOC-001">> |-> 0]  (Sale)
State 3: stock = [<<"SKU-001", "LOC-001">> |-> -1] (AdjustStock)  ← 違反!
```

### 修正アプローチ

1. **Interpretation にガードを追加**
   ```purescript
   interpretAdjust (AdjustStock tid sid delta k) = do
     current <- readStock tid sid
     if unwrap current + unwrap delta >= 0
       then do
         newQty <- writeStock tid sid (current + delta)
         pure (k newQty)
       else throwError InsufficientStock
   ```

2. **語彙を TryAdjust に変更**
   ```purescript
   data InventoryF a
     = ...
     | TryAdjust ThingId SubjectId QuantityDelta (Maybe Quantity -> a)
   ```

## Arrow と分岐禁止の意義

### なぜ ArrowChoice を禁止するか

```purescript
-- ❌ 禁止: Intent 内での分岐
badIntent = do
  stock <- getStock tid sid
  if stock.available > 0
    then adjustStock tid sid (QuantityDelta (-1))  -- 分岐!
    else pure stock
```

```purescript
-- ✅ 推奨: Interpretation での分岐
goodIntent = getStock tid sid >>> arr _.quantity

-- Interpretation
interpretWithValidation = case _ of
  GetStock tid sid k -> do
    info <- getStockFromDB tid sid
    -- 分岐は Interpretation の責務
    if info.available > 0
      then ...
      else ...
```

### TLA+ での利点

- **状態空間が線形**: 分岐がないため 2^n の爆発がない
- **検証可能**: 有限時間でモデルチェックが完了
- **1:1 対応**: Intent の構造が TLA+ Action に直接写像

## 参考資料

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- Hughes, J. "Generalising monads to arrows"
- Lamport, L. "Specifying Systems"
