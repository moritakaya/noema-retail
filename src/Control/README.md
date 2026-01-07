# Control

## 役割

Arrow 型クラスと関連するカテゴリカルな制御構造を提供する。Noema DSL の基盤となる圏論的抽象を実装。

## 圏論的位置づけ

- **圏**: Prof（profunctor の bicategory）上の構造
- **関手的関係**: Category から Arrow への強化
- **特性**: Strong monad on Prof

```
Arrow : Category → Prof
      = Promonad with strength
```

## 主要コンポーネント

| ファイル | 役割 |
|---------|------|
| `Arrow.purs` | Arrow 型クラスと基本インスタンス |

## Arrow 型クラス

```purescript
class Category a <= Arrow a where
  arr :: forall b c. (b -> c) -> a b c
  first :: forall b c d. a b c -> a (Tuple b d) (Tuple c d)

-- 導出操作
second :: forall a b c d. Arrow a => a b c -> a (Tuple d b) (Tuple d c)
(***) :: forall a b c b' c'. Arrow a => a b c -> a b' c' -> a (Tuple b b') (Tuple c c')
(&&&) :: forall a b c c'. Arrow a => a b c -> a b c' -> a b (Tuple c c')
```

## 意図的に除外: ArrowChoice

Noema では ArrowChoice を実装しない：

```purescript
-- これは実装しない
class Arrow a <= ArrowChoice a where
  left :: forall b c d. a b c -> a (Either b d) (Either c d)
```

理由：
1. **分岐禁止**: Intent は静的構造、分岐は Cognition の責務
2. **TLA+ 対応**: 分岐なしの構造は TLA+ でモデル検証が容易
3. **設計原則**: 「実行は忘却である」を型レベルで保証

## Arrow 法則

Arrow は以下の法則を満たす：

```purescript
-- 恒等
arr id = id

-- 合成
arr (g <<< f) = arr f >>> arr g

-- first 恒等
first (arr f) = arr (first f)

-- first 交換
first (f >>> g) = first f >>> first g

-- 強度
first f >>> arr fst = arr fst >>> f
```

## TLA+ 対応

Arrow 操作は TLA+ 構造に対応：

| Arrow | TLA+ |
|-------|------|
| `f >>> g` | F ∘ G（逐次合成） |
| `f *** g` | F ∧ G（並列合成） |
| `arr f` | vars' = f(vars)（純粋変換） |

## 使用例

```purescript
import Control.Arrow (arr, (>>>), (***))

-- 逐次合成
sequential :: Intent f Unit c
sequential = op1 >>> op2 >>> op3

-- 並列合成
parallel :: Intent f (Tuple a b) (Tuple c d)
parallel = op1 *** op2

-- 純粋変換の持ち上げ
transform :: Intent f a b
transform = arr (\x -> processValue x)
```

## 関連

- [../Noema/Vorzeichnung/](../Noema/Vorzeichnung/README.md) - Arrow-based Intent
- [../Noema/Vorzeichnung/FreerArrow.purs](../Noema/Vorzeichnung/FreerArrow.purs) - Freer Arrow 実装
