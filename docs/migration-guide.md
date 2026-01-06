# Monad から Arrow への移行ガイド

## 概要

現在の Freer Monad ベースの Intent を Freer Arrow ベースに移行する。
これにより「前の結果を見て分岐」を型レベルで禁止する。

## 変更の要約

| 項目 | 旧（Monad） | 新（Arrow） |
|------|-------------|-------------|
| 基本型 | `Intent f a` | `Intent' f i o` |
| 持ち上げ | `liftIntent :: f a -> Intent f a` | `liftEffect :: f i o -> Intent' f i o` |
| 合成 | `do { x <- f; g x }` | `f >>> g` |
| 純粋関数 | `pure f` | `arrIntent f` |
| 分岐 | 可能（`if/case`） | 禁止（型エラー） |

## 語彙（Vocabulary）の移行

### 旧: 単項関手

```purescript
-- 旧: f :: Type -> Type
data InventoryF a
  = GetStock ThingId (Quantity -> a)
  | AdjustStock ThingId QuantityDelta a
  | SetStock ThingId Quantity a
```

### 新: 二項関手

```purescript
-- 新: f :: Type -> Type -> Type
data InventoryF i o
  = GetStock ThingId LocationId (i -> Unit) (StockInfo -> o)
  | AdjustStock ThingId LocationId (i -> QuantityDelta) (Quantity -> o)
  | SetStock ThingId LocationId (i -> Quantity) (Unit -> o)
```

### 変換パターン

```
旧: data F a = Op ArgType (ResultType -> a)
新: data F i o = Op ArgType (i -> InputType) (ResultType -> o)

ここで:
- i: Intent に入力される型
- o: Intent から出力される型
- InputType: 操作に必要な入力（しばしば Unit）
- ResultType: 操作の結果
```

## Intent の書き換え

### パターン 1: 単純な操作

```purescript
-- 旧
getStock :: ThingId -> Intent InventoryF Quantity
getStock tid = liftIntent (GetStock tid identity)

-- 新
getStock :: ThingId -> LocationId -> Intent' InventoryF Unit StockInfo
getStock tid lid = liftEffect (GetStock tid lid identity identity)
```

### パターン 2: 結果を使う合成

```purescript
-- 旧（do 記法）
processOrder :: ThingId -> Intent InventoryF Unit
processOrder tid = do
  qty <- getStock tid
  adjustStock tid (QuantityDelta (-1))
  pure unit

-- 新（Arrow 合成）
processOrder :: ThingId -> LocationId -> Intent' InventoryF Unit Quantity
processOrder tid lid =
  getStock tid lid
  >>> arrIntent (\info -> info.quantity)
  >>> arrIntent (\(Quantity q) -> QuantityDelta (-1))
  >>> adjustStock tid lid
```

### パターン 3: 並列取得

```purescript
-- 旧
getBoth :: ThingId -> ThingId -> Intent InventoryF (Tuple Quantity Quantity)
getBoth tid1 tid2 = do
  q1 <- getStock tid1
  q2 <- getStock tid2
  pure (Tuple q1 q2)

-- 新（Arrow 並列合成）
getBoth :: ThingId -> ThingId -> LocationId -> Intent' InventoryF Unit (Tuple StockInfo StockInfo)
getBoth tid1 tid2 lid =
  getStock tid1 lid &&& getStock tid2 lid
```

### パターン 4: 分岐（禁止→Handler へ移動）

```purescript
-- 旧（Monad では可能だった分岐）
checkAndAdjust :: ThingId -> Intent InventoryF Unit
checkAndAdjust tid = do
  qty <- getStock tid
  if qty > Quantity 0
    then adjustStock tid (QuantityDelta (-1))  -- ← 分岐！
    else pure unit

-- 新: Intent では分岐禁止
-- 分岐は Handler（Cognition）で処理

-- Step 1: Intent は線形に
checkStock :: ThingId -> LocationId -> Intent' InventoryF Unit StockInfo
checkStock = getStock

-- Step 2: Handler で分岐を処理
handleCheckAndAdjust :: StockInfo -> Aff Unit
handleCheckAndAdjust info =
  if info.available > Quantity 0
    then runAdjust info.thingId info.locationId (QuantityDelta (-1))
    else pure unit

-- Step 3: 組み合わせて使用
processWithBranching :: ThingId -> LocationId -> Aff Unit
processWithBranching tid lid = do
  info <- runHandler inventoryHandler (checkStock tid lid) unit
  handleCheckAndAdjust info
```

## Handler の移行

### 旧: 自然変換

```purescript
-- 旧: f ~> m
inventoryHandler :: InventoryF ~> Aff
inventoryHandler (GetStock tid k) = do
  qty <- getFromDB tid
  pure (k qty)
inventoryHandler (AdjustStock tid delta next) = do
  adjustInDB tid delta
  pure next
```

### 新: Arrow 準同型

```purescript
-- 新: forall a b. f a b -> a -> m b
inventoryHandler :: forall a b. InventoryF a b -> a -> Aff b
inventoryHandler (GetStock tid lid fi fo) input = do
  let _ = fi input  -- 入力を消費（通常は Unit）
  info <- getFromDB tid lid
  pure (fo info)
inventoryHandler (AdjustStock tid lid fi fo) input = do
  let delta = fi input
  newQty <- adjustInDB tid lid delta
  pure (fo newQty)
```

## スマートコンストラクタの移行

```purescript
-- 旧
module Noema.Domain.Inventory where

getStock :: ThingId -> Intent InventoryF Quantity
adjustStock :: ThingId -> QuantityDelta -> Intent InventoryF Unit

-- 新
module Noema.Vorzeichnung.Vocabulary.InventoryF where

getStock :: ThingId -> LocationId -> Intent' InventoryF Unit StockInfo
adjustStock :: ThingId -> LocationId -> Intent' InventoryF QuantityDelta Quantity
setStock :: ThingId -> LocationId -> Intent' InventoryF Quantity Unit
```

## Import の変更

```purescript
-- 旧
import Noema.Vorzeichnung.Freer (Intent, liftIntent, foldIntent)
import Prelude (bind, pure, (>>=))

-- 新
import Noema.Vorzeichnung.Intent (Intent', liftEffect, runIntent, arrIntent, (>>>), (<<<), first, (&&&), (***))
-- do 記法は使用しない
```

## 移行チェックリスト

### Phase 1: 型の移行

- [ ] `FreerArrow.purs` を追加
- [ ] `Intent.purs` を新しい Arrow ベースに置き換え
- [ ] 語彙を二項関手に変換
  - [ ] `InventoryF`
  - [ ] `HttpF`
  - [ ] `StorageF`

### Phase 2: スマートコンストラクタの移行

- [ ] 各語彙のスマートコンストラクタを更新
- [ ] 型シグネチャを `Intent' f i o` 形式に

### Phase 3: Intent の書き換え

- [ ] `do` 記法を `>>>` に変換
- [ ] `if/case` を Handler に移動
- [ ] 並列取得を `&&&` に変換

### Phase 4: Handler の移行

- [ ] Handler の型を変更
- [ ] 分岐ロジックを Handler に集約

### Phase 5: テストの更新

- [ ] Monad 法則テスト → Arrow 法則テスト
- [ ] ArrowChoice 不在の検証追加

## 注意事項

### 分岐の扱い

Arrow では分岐が禁止されるため、条件分岐が必要な場合は:

1. **Handler で処理**: Intent の結果を受けて Handler で分岐
2. **複数の Intent**: 分岐ごとに異なる Intent を用意
3. **データで表現**: 分岐を Either/Maybe としてデータで表現し、後で処理

### パフォーマンス

Arrow の合成は結合法則を満たすため、左結合・右結合どちらでも結果は同じ。
ただし、実装によっては結合方向でパフォーマンスが異なる場合がある。

### デバッグ

Arrow ベースのコードは型が複雑になりがち。
型エラーが発生した場合は、中間型を明示的にアノテーションすると解決しやすい。

```purescript
step1 :: Intent' InventoryF Unit StockInfo
step1 = getStock tid lid

step2 :: Intent' InventoryF StockInfo Quantity
step2 = arrIntent (\info -> info.quantity)

combined :: Intent' InventoryF Unit Quantity
combined = step1 >>> step2
```
