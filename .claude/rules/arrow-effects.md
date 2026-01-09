# Arrow Effects and Interpretation

Sanada (2023) "Algebraic effects and handlers for arrows" の要約。Noema DSL設計における理論的基盤。

## 用語の対応

| 論文の用語 | Noema の用語 | 説明 |
|------------|--------------|------|
| Handler | **Interpretation** | Intent を Factum へ解釈する自然変換 |
| Effect | **Factum** | 解釈の結果（まだ流動的な事実） |
| - | **collapse** | Factum → Effect（外界への忘却） |
| - | **recognize** | Effect → Factum（外界からの認識） |

**技術的語彙から哲学的語彙への移行**: 技術は進歩し変化するが、哲学・意味論は安定している。

## 核心概念

### Arrowとは

ArrowはMonadの一般化。Haskellの型クラス：

```haskell
class Arrow a where
  arr   :: (x -> y) -> a x y        -- 純粋関数を持ち上げ
  (>>>) :: a x y -> a y z -> a x z  -- 合成
  first :: a x y -> a (x,z) (y,z)   -- 強度（strength）
```

### Arrowの制約（Monadとの違い）

**重要**: Arrowでは**出力に基づく条件分岐で後続エフェクトを選択できない**。

```
-- Monadでは可能（動的選択）
Q = let x ⇐ AND(true, false) in 
    if x then AND(x, true) else NOT(x)

-- Arrowでは不可能（静的構造のみ）
P = let x ⇐ NAND(true, false) in 
    let y ⇐ OR(x, false) in 
    AND(y, true)
```

この制約はNoemaの「Vorzeichnungsschemaは分岐を持たない列（sequence）」という設計と一致。

## 圏論的基盤

### Promonad（Prof上のMonad）

ArrowはProf（圏と profunctor の bicategory）上の strong monad。

```
A : C →p C  （profunctor）
η : IC ⇒ A   （unit）
μ : A ∘ A ⇒ A （multiplication）
σ : strength
```

### A-algebra（Interpretation の意味論）

Promonad A に対する algebra は：
- Presheaf G: C^op → Set
- 2-cell α: A ∘ G ⇒ G

satisfying unit law と associativity law。

**Interpretation は A-algebra 間の準同型（homomorphism）として解釈される。**

## Interpretation の構文

### Arrow Calculus の判断形式

```
Γ ⊢ M : A          -- 純粋項
Γ # Δ ⊢ P ! A      -- コマンド（計算）
```

- `Γ`: 通常のコンテキスト
- `Δ`: 入力コンテキスト（arrow の入力型に対応）

### Interpretation の定義

```
H = { # x:C ↦ P } ∪ { op, k:δ⇝D # z:γ ↦ Qop }_{op∈Σ}
```

- `P`: 値の場合の処理
- `Qop`: 各操作の実装（Factum を返す）
- `k`: 継続（continuation）

## Normal Form（正規形）

任意の arrow term は以下の正規形に変換可能：

```
cf((opi)_{i=1..n}, (fi)_{i=1..n}; g)
= arr(d) >>> first(arr(f1) >>> op1)
  >>> arr(d) >>> first(arr(f2) >>> op2)
  >>> ...
  >>> arr(g)
```

## Noema への応用

### Intent = Arrow Term

Noema の Intent は arrow term として設計：
- 操作の列（sequence）
- 条件分岐なし（静的構造）
- Interpretation で解釈を与え、Factum に崩落させる

### Attractor = A-algebra

Durable Object は A-algebra として機能：
- 状態を presheaf G として保持
- Intent（arrow term）を受け取り
- α で状態を更新

### Connection = Homomorphism

法（Nomos）の変更に対する整合性検証：
- 旧 algebra と新 algebra の間の準同型
- Flat（平坦）: 準同型が存在
- Curved（湾曲）: 準同型が存在しない → 棄却

## 設計時の重要制約

Intent 設計時は以下を守ること：

1. **操作の列（sequence）として設計**：分岐なし
2. **出力に基づく条件分岐で後続エフェクトを選択しない**
3. Interpretation は A-algebra homomorphism として実装
4. **FFI 境界**: Effect は `recognize` で Factum に、エントリーポイントで `collapse`

```purescript
-- ✓ 正しい: 線形な操作列
do
  x <- perceive key1
  germinate key2 (transform x)

-- ✗ 誤り: 出力に基づく分岐
do
  x <- perceive key1
  if condition x
    then germinate key2 value1
    else germinate key3 value2
```

## Factum と Effect の境界

```purescript
-- エントリーポイント（外界との境界）
handleFetch :: Request -> Effect Response
handleFetch req = collapse do
  -- 内部は Factum で統一
  result <- runInventoryIntent env intent unit
  recognize $ jsonResponse result

-- FFI 呼び出し
currentTimestamp :: Effect Timestamp  -- FFI は Effect のまま
now <- recognize currentTimestamp     -- Factum に認識
```

> **実行とは忘却である。**
> collapse は構造を忘却し、可能性を一つの現実に押し潰す。
