# Freer Arrow 設計文書

## 概要

Noema の Intent を Freer Arrow として再設計する。
これにより「前の結果を見て分岐」を型レベルで禁止する。

## 圏論的基盤

### Arrow の定義

Arrow は以下の構造を持つ:

```
class Category a <= Arrow a where
  arr   :: (b -> c) -> a b c           -- 純粋関数の埋め込み
  first :: a b c -> a (b, d) (c, d)    -- 強度
```

派生操作:
```
second :: a b c -> a (d, b) (d, c)
second f = arr swap >>> first f >>> arr swap

(***) :: a b c -> a b' c' -> a (b, b') (c, c')
f *** g = first f >>> second g

(&&&) :: a b c -> a b c' -> a b (c, c')
f &&& g = arr (\x -> (x, x)) >>> (f *** g)
```

### ArrowChoice（Noema では禁止）

```
class Arrow a <= ArrowChoice a where
  left  :: a b c -> a (Either b d) (Either c d)
  right :: a b c -> a (Either d b) (Either d c)
```

**Noema では ArrowChoice を実装しない。**
これにより以下のコードが型エラーになる:

```purescript
-- 型エラー: No instance for ArrowChoice Intent
illegalBranching = left getStock
```

### Freer Arrow の構成

Freer Monad が自由モナドを構成するように、
Freer Arrow は自由 Arrow を構成する:

```
data FreerArrow f a b where
  Arr    :: (a -> b) -> FreerArrow f a b
  LiftF  :: f a b -> FreerArrow f a b
  Compose :: FreerArrow f b c -> FreerArrow f a b -> FreerArrow f a c
  First  :: FreerArrow f a b -> FreerArrow f (a, d) (b, d)
```

または、より効率的な表現:

```
-- Cayley 表現（合成の効率化）
newtype FreerArrow f a b = FreerArrow (forall c. FreerArrow' f b c -> FreerArrow' f a c)

data FreerArrow' f a b where
  Id     :: FreerArrow' f a a
  Arr'   :: (a -> b) -> FreerArrow' f b c -> FreerArrow' f a c
  Effect :: f a b -> FreerArrow' f b c -> FreerArrow' f a c
  First' :: FreerArrow' f a b -> FreerArrow' f (a, d) (b, d)
```

## 語彙（Vocabulary）の再設計

現在の語彙は単項関手 `f :: Type -> Type`:

```purescript
-- 旧: 単項関手
data InventoryF a
  = GetStock ThingId (Quantity -> a)
  | AdjustStock ThingId QuantityDelta a
```

Arrow では二項関手 `f :: Type -> Type -> Type` が必要:

```purescript
-- 新: 二項関手（Profunctor）
data InventoryF a b where
  GetStock    :: ThingId -> InventoryF () Quantity
  AdjustStock :: ThingId -> QuantityDelta -> InventoryF () ()
  SetStock    :: ThingId -> InventoryF Quantity ()
```

または、入力を明示した形式:

```purescript
data InventoryF a b
  = GetStock ThingId (a -> ()) (Quantity -> b)
  | AdjustStock ThingId QuantityDelta (a -> ()) (() -> b)
  | SetStock ThingId (a -> Quantity) (() -> b)
```

## Handler の再設計

Handler は Arrow 準同型:

```purescript
type Handler f g = forall a b. f a b -> g a b

-- 制約: Arrow 構造を保存
-- h (arr f) = arr f
-- h (f >>> g) = h f >>> h g
-- h (first f) = first (h f)
```

具体的な Handler:

```purescript
inventoryHandler :: InventoryF ~> Aff
inventoryHandler (GetStock thingId) = Aff \_ -> do
  -- SQLite からの読み取り
  ...
inventoryHandler (AdjustStock thingId delta) = Aff \_ -> do
  -- SQLite への書き込み
  ...
```

## Intent の使用例

```purescript
-- 合法: 線形な合成
processOrder :: Intent InventoryF () ()
processOrder =
  getStock "SKU-001"
  >>> arr (\qty -> qty - 1)
  >>> setStock "SKU-001"

-- 合法: 並列合成
parallelGet :: Intent InventoryF () (Quantity, Quantity)
parallelGet =
  getStock "SKU-001" &&& getStock "SKU-002"

-- 不正: 分岐（型エラー）
-- illegalBranching =
--   getStock "SKU-001"
--   >>> left (adjustStock "SKU-001" (-1))  -- 型エラー!
```

## 移行計画

### Phase 1: Freer Arrow 基盤

1. `FreerArrow.purs` の実装
2. `Vocabulary` の二項関手への変換
3. 基本的な Arrow インスタンス

### Phase 2: 語彙の移行

1. `InventoryF` の再設計
2. `HttpF`, `StorageF` の再設計
3. 余積の再定義

### Phase 3: Handler の移行

1. Arrow 準同型としての Handler
2. 既存 Handler の書き換え

### Phase 4: 既存コードの移行

1. `do` 記法から `>>>` への変換
2. 分岐コードの検出と修正
3. テストの更新

## 参考文献

- [Arrow Effects] Hughes, J. "Generalising monads to arrows"
- [Freer Arrow] Lindley, S. "Algebraic effects and handlers"
- [Profunctor] Milewski, B. "Profunctor optics"
