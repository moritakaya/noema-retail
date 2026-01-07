# Noema 設計原理

## 核心命題

> **プログラムとは、主体が世界に対して投げかける意志を、Vorzeichnungsschema として構造化し、認知（Cognition）による忘却を通じて事実へと崩落させる、対話的運動である。**

> **実行とは忘却である。**

## 1. 圏論的基盤

### 1.1 Intent ⊣ Cognition 随伴

Noema の核心は随伴関手のペアである：

```
Intent    : Prop → Struct    （左随伴・自由関手）
Cognition : Struct → Prop    （右随伴・忘却関手）
```

| 圏 | 対象 | 解釈 |
|---|---|---|
| **Prop** | 論理命題 | 認知可能な事実の空間 |
| **Struct** | 命題 + 意志の木構造 | 意図の構造化された空間 |

自然同型：

```
Hom_Struct(Intent(P), S) ≅ Hom_Prop(P, Cognition(S))
```

「意図 P を構造 S に到達させる道筋」と「構造 S を認知して P から理解する道筋」が自然に対応する。

### 1.2 三層構造

| 層 | 構造 | 解釈 |
|---|---|---|
| 原初的意志 | Functor f | 構造化されていない意図の断片 |
| Vorzeichnungsschema | Arrow Effects | 認知を予期して構造化された意志 |
| 実行結果 | Effect | 構造が忘却され事実に崩落した状態 |

## 2. Arrow Effects（分岐禁止）

### 2.1 なぜ Monad ではなく Arrow か

**Monad** では出力に基づく動的分岐が可能：

```purescript
-- Monad: 動的分岐
do
  x <- operation1
  if condition x
    then operation2
    else operation3
```

**Arrow Effects** では静的構造のみ：

```purescript
-- Arrow: 静的構造（分岐禁止）
operation1 >>> operation2 >>> operation3
```

### 2.2 ArrowChoice の意図的な除外

```purescript
-- これは実装しない
class Arrow a <= ArrowChoice a where
  left :: forall b c d. a b c -> a (Either b d) (Either c d)
```

この制約により：

1. **実行前確定**: Intent の全構造が実行前に確定
2. **TLA+ 対応**: 分岐なしの構造はモデル検証が容易
3. **設計原則**: 「実行は忘却である」を型レベルで保証
4. **関心の分離**: 分岐ロジックは Cognition（Handler）の責務

### 2.3 理論的背景

Sanada (2023) "Algebraic effects and handlers for arrows" に基づく：

- Arrow は Prof（profunctor の bicategory）上の strong monad
- Handler は A-algebra 間の準同型（homomorphism）
- 任意の arrow term は正規形に変換可能

## 3. Vorzeichnung（前描画）

### 3.1 概念

Husserl の現象学から着想：

- **Vorzeichnung**: 「前描画」- 実行前のスキーマ
- 可能性の樹形図を保存
- まだ認知（忘却）されていない純粋な意志構造

### 3.2 実装

```purescript
newtype Intent f a b = Intent (FreerArrow f a b)

-- スマートコンストラクタ
liftEffect :: forall f a. f a -> Intent f Unit a
```

### 3.3 特性

1. **静的構造**: 実行前に全構造が確定
2. **合成可能**: Arrow 則により合成が自然
3. **検証可能**: TLA+ でモデル検証可能

## 4. Cognition（認知・忘却）

### 4.1 Handler の意味論

Handler は自然変換として定義：

```purescript
type Handler f m = forall a. f a -> m a
```

A-algebra homomorphism として解釈：

- 入力: Intent（意志の構造）
- 出力: Effect（事実）
- 変換: 構造の「忘却」

### 4.2 TLA+ ガードの実装

TLA+ モデル検証で発見されたガードを Handler に実装：

```purescript
-- ReserveStock: reserved + qty <= MaxQuantity
-- ReleaseReservation: stock + qty <= MaxQuantity
```

これにより形式仕様と実装の整合性を保証。

## 5. Arrow-TLA+ 対応

| 概念 | PureScript | TLA+ |
|------|------------|------|
| 逐次合成 | `f >>> g` | F ∘ G |
| 並列合成 | `f *** g` | F ∧ G |
| 純粋変換 | `arr f` | vars' = f(vars) |
| 効果 | `liftEffect` | Action |

## 6. 設計原則まとめ

1. **随伴の保存**: Vorzeichnung/ ⊣ Cognition/ が明示的
2. **分岐禁止**: Arrow Effects で静的構造を強制
3. **関手の局所性**: 語彙は Vocabulary/ に集約
4. **技術非依存**: Noema/ は Platform/ に依存しない
5. **形式検証**: TLA+ でモデル検証、ガードを Handler に反映
6. **Presheaf 構造**: Inventory : Channel^op → Set

## 参考文献

- Sanada, T. (2023). "Algebraic effects and handlers for arrows"
- Husserl, E. "Ideas: General Introduction to Pure Phenomenology"
- Lamport, L. "Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers"
