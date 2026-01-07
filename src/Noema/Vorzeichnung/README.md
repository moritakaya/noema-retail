# Vorzeichnung

## 役割

Intent（意図）の静的構造を定義する。Husserl の現象学における「前描画」から着想を得た、実行前に構造が確定するスキーマ。

## 圏論的位置づけ

- **圏**: Intent 圏（Arrow Effects の対象）
- **関手的関係**: Intent → Cognition への自然変換の domain
- **随伴での位置**: 左随伴（自由関手）側

```
Vorzeichnung : Vocabulary → Intent
             = Arrow-based Freer construction
```

Arrow Effects により、出力に基づく分岐が型レベルで禁止される。これにより：
- 実行前に Intent の全構造が確定
- TLA+ でのモデル検証が容易
- 「実行は忘却である」を実現

## 主要コンポーネント

| ファイル | 役割 |
|---------|------|
| `Intent.purs` | Arrow-based Intent 型定義 |
| `FreerArrow.purs` | Freer Arrow 実装 |
| `Combinators.purs` | Arrow コンビネータ（`>>>`, `***`, `arr`） |
| `Vocabulary/` | ドメイン固有の操作語彙 |

## Arrow Effects

### 型定義

```purescript
newtype Intent f a b = Intent (FreerArrow f a b)

-- Arrow インスタンス（ArrowChoice なし）
instance Arrow (Intent f)
instance Category (Intent f)
```

### なぜ ArrowChoice を実装しないか

Monad では出力に基づく分岐が可能：

```purescript
-- Monad: 動的分岐
do
  x <- operation1
  if condition x
    then operation2
    else operation3
```

Arrow Effects では静的構造のみ：

```purescript
-- Arrow: 静的構造（分岐禁止）
operation1 >>> operation2 >>> operation3
```

この制約により、Intent は実行前に全構造が確定する。

## 使用例

```purescript
import Noema.Vorzeichnung.Intent (Intent, liftEffect)
import Noema.Vorzeichnung.Vocabulary.InventoryF (getStock, setStock)

-- 在庫確認して更新する Intent
checkAndUpdate :: ThingId -> LocationId -> Intent InventoryF Unit Unit
checkAndUpdate tid lid =
  getStock tid lid >>> arr (\info -> Quantity (info.quantity + 10)) >>> setStock tid lid
```

## 関連

- [Vocabulary/](Vocabulary/README.md) - ドメイン語彙
- [../Cognition/](../Cognition/README.md) - Intent の解釈
- [../../Control/](../../Control/README.md) - Arrow 型クラス
