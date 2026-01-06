# Intent ↔ TLA+ 双方向検証パイプライン

## 概要

Noema の Intent（Freer Arrow）と TLA+ 仕様の間に圏論的対応を構築し、
自動変換と双方向検証を実現する。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Noema Verification Pipeline                       │
│                                                                      │
│  ┌──────────────┐         ┌──────────────┐         ┌──────────────┐ │
│  │   Intent     │ ──────→ │  TLA+ Spec   │ ──────→ │   TLC        │ │
│  │ (PureScript) │ extract │   (.tla)     │  check  │ Model Check  │ │
│  └──────────────┘         └──────────────┘         └──────────────┘ │
│         ↑                        │                        │         │
│         │                        ▼                        ▼         │
│         │                 ┌──────────────┐         ┌──────────────┐ │
│         │                 │  Invariants  │         │ Counterexample│ │
│         │                 │  Liveness    │         │   Trace      │ │
│         │                 └──────────────┘         └──────────────┘ │
│         │                                                 │         │
│         └────────────── feedback ─────────────────────────┘         │
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

## モジュール構成

```
noema-retail/
├── tlaplus/
│   ├── extract/                    # PureScript → TLA+ 抽出
│   │   ├── Extractor.purs          # AST 解析
│   │   ├── TlaGen.purs             # TLA+ コード生成
│   │   └── Mapping.purs            # 型マッピング
│   │
│   ├── specs/                      # 生成された TLA+ 仕様
│   │   ├── Inventory.tla           # 在庫モジュール
│   │   ├── Inventory.cfg           # TLC 設定
│   │   └── InventoryProps.tla      # 性質定義
│   │
│   ├── properties/                 # 検証すべき性質
│   │   ├── Safety.tla              # 安全性（不変条件）
│   │   ├── Liveness.tla            # 活性（進行保証）
│   │   └── Fairness.tla            # 公平性
│   │
│   └── feedback/                   # 反例からのフィードバック
│       ├── TraceParser.purs        # TLC 出力解析
│       └── Diagnostics.purs        # エラー診断
│
├── src/Noema/
│   └── Vorzeichnung/
│       ├── Freer.purs              # Freer Arrow
│       └── Vocabulary/
│           └── InventoryF.purs     # 在庫語彙
│
└── .github/workflows/
    └── tla-check.yml               # CI/CD 統合
```

## Phase 1: Intent → TLA+ 抽出

### 1.1 語彙の TLA+ 表現

各語彙（Functor）を TLA+ の Action に対応付ける。

```purescript
-- PureScript: 語彙定義
data InventoryF a b where
  GetStock    :: ProductId -> InventoryF Unit Quantity
  SetStock    :: ProductId -> InventoryF Quantity Unit
  AdjustStock :: ProductId -> QuantityDelta -> InventoryF Unit Quantity
  ReserveStock :: ProductId -> Quantity -> InventoryF Unit Boolean
```

```tla
---- MODULE InventoryActions ----
VARIABLES stock, reserved

\* GetStock: 読み取り専用
GetStock(pid) ==
  /\ UNCHANGED <<stock, reserved>>
  \* 戻り値: stock[pid]

\* SetStock: 書き込み
SetStock(pid, qty) ==
  /\ stock' = [stock EXCEPT ![pid] = qty]
  /\ UNCHANGED reserved

\* AdjustStock: 差分更新
AdjustStock(pid, delta) ==
  /\ stock' = [stock EXCEPT ![pid] = @ + delta]
  /\ UNCHANGED reserved

\* ReserveStock: 条件付き予約
ReserveStock(pid, qty) ==
  \/ /\ stock[pid] >= qty
     /\ stock' = [stock EXCEPT ![pid] = @ - qty]
     /\ reserved' = [reserved EXCEPT ![pid] = @ + qty]
  \/ /\ stock[pid] < qty
     /\ UNCHANGED <<stock, reserved>>

====
```

### 1.2 Intent の TLA+ 変換

```purescript
-- PureScript: Intent
saleIntent :: Intent InventoryF Unit Quantity
saleIntent =
  getStock (ProductId "SKU-001")
  >>> arr (\qty -> (qty, QuantityDelta (-1)))
  >>> first (adjustStock (ProductId "SKU-001"))
  >>> arr snd
```

↓ 自動変換

```tla
---- MODULE SaleIntent ----
EXTENDS InventoryActions

\* saleIntent の TLA+ 表現
SaleIntent ==
  LET pid == "SKU-001"
      currentQty == stock[pid]
      newQty == currentQty - 1
  IN
    /\ AdjustStock(pid, -1)
    \* 戻り値: newQty
```

### 1.3 抽出アルゴリズム

```purescript
-- Intent を TLA+ に変換
extractTla :: forall f a b. Intent f a b -> TlaModule
extractTla intent = case unwrap intent of
  Arr f -> 
    -- 純粋関数: UNCHANGED
    TlaUnchanged
    
  Eff effect ->
    -- 効果: 対応する Action を生成
    effectToAction effect
    
  Seq first second ->
    -- 列合成: 逐次実行
    TlaSeq (extractTla first) (extractTla second)
    
  Par inner ->
    -- 並列合成: 同時実行
    TlaPar (extractTla inner)
```

## Phase 2: 性質の定義

### 2.1 安全性（Safety）

「悪いことが決して起きない」

```tla
---- MODULE InventorySafety ----
EXTENDS Inventory

\* 不変条件 1: 在庫は非負
NonNegativeStock ==
  \A pid \in DOMAIN stock: stock[pid] >= 0

\* 不変条件 2: 予約は在庫を超えない
ReservationBound ==
  \A pid \in DOMAIN stock: reserved[pid] <= stock[pid]

\* 不変条件 3: 総在庫の保存（閉じたシステムの場合）
TotalConservation ==
  LET total == Sum([pid \in DOMAIN stock |-> stock[pid] + reserved[pid]])
  IN total = INITIAL_TOTAL

\* 全不変条件
Invariants ==
  /\ NonNegativeStock
  /\ ReservationBound

====
```

### 2.2 活性（Liveness）

「良いことがいつか起きる」

```tla
---- MODULE InventoryLiveness ----
EXTENDS Inventory

\* 活性 1: 予約された在庫はいつか解放される
ReservationEventuallyReleased ==
  \A pid \in DOMAIN reserved:
    reserved[pid] > 0 ~> reserved[pid] = 0

\* 活性 2: リクエストはいつか処理される
RequestEventuallyProcessed ==
  \A req \in PendingRequests:
    req \in PendingRequests ~> req \notin PendingRequests

====
```

### 2.3 公平性（Fairness）

```tla
---- MODULE InventoryFairness ----
EXTENDS Inventory

\* 弱公平性: 有効なアクションはいつか実行される
WeakFairness ==
  WF_vars(AdjustStock)

\* 強公平性: 無限に有効なアクションは無限に実行される
StrongFairness ==
  SF_vars(ReserveStock)

====
```

## Phase 3: TLC による検証

### 3.1 設定ファイル

```
---- CONFIG Inventory ----
SPECIFICATION Spec
INVARIANTS
  NonNegativeStock
  ReservationBound
PROPERTIES
  ReservationEventuallyReleased
CONSTANTS
  ProductIds = {"SKU-001", "SKU-002", "SKU-003"}
  MaxQuantity = 100
====
```

### 3.2 CI/CD 統合

```yaml
# .github/workflows/tla-check.yml
name: TLA+ Verification

on:
  push:
    paths:
      - 'src/Noema/Vorzeichnung/**'
      - 'tlaplus/**'

jobs:
  extract:
    name: Extract TLA+ from Intent
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup PureScript
        uses: purescript-contrib/setup-purescript@main
      
      - name: Build extractor
        run: spago build --main TlaPlus.Extract.Main
      
      - name: Extract TLA+ specs
        run: spago run --main TlaPlus.Extract.Main
      
      - name: Upload specs
        uses: actions/upload-artifact@v4
        with:
          name: tla-specs
          path: tlaplus/specs/

  model-check:
    name: TLC Model Checking
    runs-on: ubuntu-latest
    needs: extract
    steps:
      - uses: actions/checkout@v4
      
      - name: Download specs
        uses: actions/download-artifact@v4
        with:
          name: tla-specs
          path: tlaplus/specs/
      
      - name: Setup TLA+
        run: |
          wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
          echo "TLA_JAR=$PWD/tla2tools.jar" >> $GITHUB_ENV
      
      - name: Run TLC
        run: |
          java -jar $TLA_JAR -config tlaplus/specs/Inventory.cfg \
               -workers auto \
               -deadlock \
               tlaplus/specs/Inventory.tla
      
      - name: Check results
        run: |
          if grep -q "Error:" tlc.out; then
            echo "::error::TLA+ verification failed"
            cat tlc.out
            exit 1
          fi

  feedback:
    name: Generate Feedback
    runs-on: ubuntu-latest
    needs: model-check
    if: failure()
    steps:
      - name: Parse counterexample
        run: spago run --main TlaPlus.Feedback.Main
      
      - name: Create issue
        uses: actions/github-script@v7
        with:
          script: |
            const fs = require('fs');
            const trace = fs.readFileSync('feedback/trace.md', 'utf8');
            github.rest.issues.create({
              owner: context.repo.owner,
              repo: context.repo.repo,
              title: 'TLA+ Verification Failed',
              body: trace,
              labels: ['tla+', 'verification']
            });
```

## Phase 4: 反例からのフィードバック

### 4.1 反例トレースの解析

TLC が反例を出力した場合、PureScript のテストケースに変換する。

```
TLC 出力:
State 1: stock = [SKU-001 |-> 10]
State 2: stock = [SKU-001 |-> 9]  (AdjustStock)
State 3: stock = [SKU-001 |-> -1] (AdjustStock)  ← 不変条件違反!
```

↓ 変換

```purescript
-- 自動生成されたテストケース
failingTrace :: Spec Unit
failingTrace = describe "TLA+ counterexample" do
  it "should not allow stock to go negative" do
    let
      intent =
        setStock (ProductId "SKU-001") (Quantity 10)
        >>> adjustStock (ProductId "SKU-001") (QuantityDelta (-1))
        >>> adjustStock (ProductId "SKU-001") (QuantityDelta (-10))
    
    result <- runIntent handler intent unit
    result `shouldSatisfy` (_ >= Quantity 0)
```

### 4.2 診断メッセージ

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
TLA+ Verification FAILED: NonNegativeStock violated

Location: src/Noema/Vorzeichnung/Vocabulary/InventoryF.purs
Intent:   adjustStock

Counterexample trace:
  1. SetStock "SKU-001" 10      → stock = 10
  2. AdjustStock "SKU-001" -1   → stock = 9
  3. AdjustStock "SKU-001" -10  → stock = -1  ❌

Suggested fix:
  Add guard in AdjustStock handler:
  
    handleAdjust pid delta = do
      current <- readStock pid
      if current + delta >= 0
        then writeStock pid (current + delta)
        else throwError InsufficientStock

Or modify vocabulary to use TryAdjust:

    data InventoryF a b where
      TryAdjust :: ProductId -> QuantityDelta -> InventoryF Unit (Maybe Quantity)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## Phase 5: 双方向の整合性

### 5.1 Refinement 検証

TLA+ の抽象仕様と具体的な Intent の間の refinement を検証。

```tla
---- MODULE InventoryRefinement ----
EXTENDS Inventory

\* 抽象仕様
AbstractSpec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

\* 具体的な Intent からの実装
ConcreteSpec ==
  /\ ConcreteInit
  /\ [][ConcreteNext]_vars
  /\ WF_vars(ConcreteNext)

\* Refinement: Concrete => Abstract
THEOREM ConcreteSpec => AbstractSpec

====
```

### 5.2 往復検証（Round-trip）

```
Intent (PureScript)
      │
      ▼ extract
TLA+ Spec
      │
      ▼ generate (optional)
Intent' (PureScript)
      │
      ▼ compare
Intent ≡ Intent' ?
```

## 実装ロードマップ

### Sprint 1 (Week 1-2): 基盤構築
- [ ] TLA+ 抽出モジュールの基本構造
- [ ] InventoryF → TLA+ の手動変換
- [ ] 基本的な不変条件の定義

### Sprint 2 (Week 3-4): 自動化
- [ ] Intent AST の解析
- [ ] TLA+ コード生成
- [ ] CI/CD パイプライン統合

### Sprint 3 (Week 5-6): 反例フィードバック
- [ ] TLC 出力のパース
- [ ] PureScript テストケース生成
- [ ] 診断メッセージ

### Sprint 4 (Week 7-8): 高度な検証
- [ ] Refinement 検証
- [ ] 活性・公平性の検証
- [ ] 往復検証

## 参考資料

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [Arrow Effects] Hughes, J. "Generalising monads to arrows"
- [Specifying Systems] Lamport, L.
