# Vocabulary

## 役割

ドメイン固有の操作語彙を Functor として定義する。各 Vocabulary は Intent 構築のための基本操作を提供する。

## 圏論的位置づけ

- **圏**: Functor 圏（Set^op → Set）
- **関手的関係**: 各 Vocabulary F から Intent への持ち上げ
- **構成**: 複数の Vocabulary は余積（Coproduct）で統合

```
Vocabulary = InventoryF + HttpF + StorageF + ...
           = Σ_i F_i (余積)
```

各 Vocabulary F に対して、Freer Arrow による自由構成：

```
liftF : F a → Intent F Unit a
```

## 主要コンポーネント

| ファイル | 語彙 | 操作 |
|---------|------|------|
| `Base.purs` | 基本型 | Timestamp, Quantity, etc. |
| `InventoryF.purs` | 在庫操作 | GetStock, SetStock, Reserve, etc. |
| `HttpF.purs` | HTTP 操作 | Fetch, Request, Response |
| `StorageF.purs` | Storage 操作 | Get, Put, Delete |
| `RetailF.purs` | 統合語彙 | 全 Vocabulary の余積 |

## Functor としての Vocabulary

```purescript
-- InventoryF: 在庫操作の Functor
data InventoryF next
  = GetStock ThingId LocationId (StockInfo -> next)
  | SetStock ThingId LocationId Quantity next
  | AdjustStock ThingId LocationId QuantityDelta (Quantity -> next)
  | ReserveStock ThingId LocationId Quantity (Boolean -> next)
  | ReleaseReservation ThingId LocationId ReservationId next
  | SyncToChannel Channel ThingId Quantity (SyncResult -> next)
  | SyncFromChannel Channel ThingId (StockInfo -> next)

derive instance Functor InventoryF
```

## スマートコンストラクタ

各操作は Intent に持ち上げるスマートコンストラクタを提供：

```purescript
-- 在庫取得
getStock :: ThingId -> LocationId -> InventoryIntent Unit StockInfo
getStock tid lid = liftEffect (GetStock tid lid identity)

-- 在庫設定
setStock :: ThingId -> LocationId -> Quantity -> InventoryIntent Unit Unit
setStock tid lid qty = liftEffect (SetStock tid lid qty unit)
```

## TLA+ 対応

各 Vocabulary 操作は TLA+ Action に対応：

| PureScript | TLA+ |
|------------|------|
| `getStock` | （観測のみ、状態変更なし） |
| `setStock` | `SetStock(pid, lid, qty)` |
| `adjustStock` | `AdjustStock(pid, lid, delta)` |
| `reserveStock` | `ReserveStock(pid, lid, qty)` |
| `releaseReservation` | `ReleaseReservation(pid, lid, qty)` |

## 使用例

```purescript
import Noema.Vorzeichnung.Vocabulary.InventoryF
  (getStock, setStock, adjustStock)

-- 在庫を確認して調整する Intent
adjustInventory :: ThingId -> LocationId -> InventoryIntent Unit Quantity
adjustInventory tid lid =
  getStock tid lid
    >>> arr (_.quantity)
    >>> arr (\q -> QuantityDelta (if q > 100 then -10 else 10))
    >>> adjustStock tid lid
```

## 関連

- [../](../README.md) - Vorzeichnung 親モジュール
- [../../Cognition/](../../Cognition/README.md) - Handler 実装
- [../../../../tlaplus/](../../../../tlaplus/README.md) - TLA+ 仕様
