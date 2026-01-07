# Cognition

## 役割

Intent（意図）を Effect（事実）へ解釈・実行する。圏論的には忘却関手として機能し、意志の構造を忘却して事実に崩落させる。

## 圏論的位置づけ

- **圏**: Cognition 圏（Effect の対象）
- **関手的関係**: Intent → Effect への自然変換
- **随伴での位置**: 右随伴（忘却関手）側

```
Cognition : Intent → Effect
          = A-algebra homomorphism
          = Handler (自然変換 f ~> m)
```

**「実行とは忘却である」**: Cognition は Intent の構造を忘却し、具体的な副作用へ変換する。

## 主要コンポーネント

| ファイル | 役割 |
|---------|------|
| `Handler.purs` | Handler 基底型（自然変換 `f ~> m`） |
| `InventoryHandler.purs` | 在庫操作の Handler 実装 |
| `StorageHandler.purs` | Storage 操作の Handler 実装 |

## Handler の型

```purescript
-- Handler は自然変換として定義
type Handler f m = forall a. f a -> m a

-- Intent を実行
runIntent :: forall f m a b. Monad m => Handler f m -> Intent f a b -> a -> m b
```

## A-algebra としての Handler

Handler は A-algebra 間の準同型（homomorphism）として解釈される：

- **A-algebra**: Presheaf G と 2-cell α: A ∘ G ⇒ G
- **Handler**: α を具体化した自然変換

TLA+ 仕様との対応：
- 各 Handler 操作は TLA+ Action に対応
- ガード条件（invariant）を Handler で実装

## 使用例

```purescript
import Noema.Cognition.InventoryHandler (runInventoryIntent, mkInventoryEnv)
import Noema.Vorzeichnung.Vocabulary.InventoryF (getStock)

-- Intent を実行
main :: Effect Unit
main = do
  let env = mkInventoryEnv sqlStorage
  let intent = getStock (ThingId "product-1") (LocationId "warehouse-1")

  -- runIntent: Intent → Effect（忘却）
  result <- runInventoryIntent env intent unit
  log $ "Stock: " <> show result.quantity
```

## TLA+ ガード実装

Handler には TLA+ モデル検証で発見されたガードを実装：

```purescript
-- ReserveStock: reserved + qty <= MaxQuantity をチェック
-- ReleaseReservation: stock + qty <= MaxQuantity をチェック
```

これにより、形式仕様と実装の整合性を保証する。

## 関連

- [../Vorzeichnung/](../Vorzeichnung/README.md) - Intent の定義
- [../../TlaPlus/](../../TlaPlus/) - TLA+ 連携
- [../../Platform/Cloudflare/](../../Platform/Cloudflare/) - Durable Object 実装
