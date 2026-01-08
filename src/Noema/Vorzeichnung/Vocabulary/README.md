# Vocabulary

## 役割

ドメイン固有の操作語彙を Functor として定義する。各 Vocabulary は Intent 構築のための基本操作を提供する。

## 圏論的位置づけ

- **圏**: Functor 圏（Set^op → Set）
- **関手的関係**: 各 Vocabulary F から Intent への持ち上げ
- **構成**: 複数の Vocabulary は余積（Coproduct）で統合

```
NoemaF = SubjectF + ThingF + RelationF + ContractF
       = Coproduct SubjectF (Coproduct ThingF (Coproduct RelationF ContractF))
```

## 四つの語彙（AVDC 構造）

| 語彙 | 圏論的位置 | 操作対象 |
|------|-----------|---------|
| SubjectF | Base 圏 | 意志を持つ主体（DO） |
| ThingF | Fiber 圏 | もの・こと（属性×位置×時間）|
| RelationF | Span 圏 | Subject-Thing 間の関係 |
| ContractF | 規定の圏 | 権利・義務、契約間関係 |

## 主要コンポーネント

| ファイル | 語彙 | 操作 |
|---------|------|------|
| `SubjectF.purs` | 意志主体 | CreateSubject, GetSubject, SendIntent |
| `ThingF.purs` | 物・時間 | GetProperty, SetProperty, GetPrimal, RegisterProtention |
| `RelationF.purs` | 関係性 | AddRelation, GetRelationsFrom, RecordOwnershipTransfer |
| `ContractF.purs` | 契約 | ProposeContract, AcceptContract, FulfillObligation |
| `NoemaF.purs` | 統合語彙 | 全 Vocabulary の余積 |
| `Constructors.purs` | スマートコンストラクタ | Intent への持ち上げ |
| `InventoryF.purs` | 在庫操作 | GetStock, SetStock, Reserve（SubjectId を使用） |
| `HttpF.purs` | HTTP 操作 | Fetch, Request, Response |
| `StorageF.purs` | Storage 操作 | Get, Put, Delete |

## ThingF の時間構造（Husserl）

```
Retention（把持）: 過去の Snapshot
Primal（原印象）: 現在の状態
Protention（予持）: 未来の Pending Intent（Alarm 連動）
```

## RelationKind 一覧

```
包摂: Contains, Guards
権利: Owns, Possesses, Claims, Secures, SharedBy
引当: Reserves, Commits, Intends
移動: Transports, Consigns
構成: ComposedOf, BundledWith, Substitutes
観測: Observes, Tracks
代理: ActsFor
制限: Restricts
```

## Contract 間の関係

```
Prerequisite（前提）: B は A がないと成立しない
Subordinate（従属）: A 終了で B も終了
Consideration（対価）: A の履行が B の対価
Security（担保）: B は A の履行を担保
Amendment（変更）: B は A を変更
Termination（解除）: B は A を解除
```

## スマートコンストラクタの使用例

```purescript
import Noema.Vorzeichnung.Vocabulary.Constructors

-- Subject を作成
createNewSubject :: NoemaIntent SubjectInit SubjectId
createNewSubject = createSubject

-- Thing の状態を取得
getInventory :: ThingId -> NoemaIntent Unit ThingState
getInventory tid = getPrimal tid

-- 関係を追加
establishOwnership :: NoemaIntent RelationInit RelationId
establishOwnership = addRelation

-- 契約を提案
proposeNewContract :: NoemaIntent ContractProposal ContractId
proposeNewContract = proposeContract
```

## 型定義の正規化

基本型は `Noema.Core.Locus` に集約されている：

| 型 | 説明 |
|---|---|
| `ThingId` | 物の識別子 |
| `SubjectId` | 意志を持つ主体の識別子（旧 LocationId を統合） |
| `Quantity` | 数量（非負整数） |
| `QuantityDelta` | 数量変化（正負あり） |

`Channel` 型は `Noema.Presheaf.Channel` に定義されている。

### 設計変更: LocationId → SubjectId

旧設計では `LocationId`（倉庫、店舗）が在庫の位置を表していた。
新設計では Subject が Thing を包摂し、
その Subject の位置が Thing の位置を決定する。

```purescript
-- 旧設計
getStock :: ThingId -> LocationId -> InventoryIntent Unit StockInfo

-- 新設計
getStock :: ThingId -> SubjectId -> InventoryIntent Unit StockInfo
```

## 実装規則

1. **Sediment のみ**: UPDATE 禁止、INSERT のみ
2. **Arrow 維持**: ArrowChoice 禁止、分岐は Handler で
3. **Source of Truth**: 所有権等は Thing を包摂する Subject が保持
4. **View**: Container の Contents はキャッシュ

## 関連

- [../](../README.md) - Vorzeichnung 親モジュール
- [../../Core/](../../Core/README.md) - 基本型と座標系
- [../../Cognition/](../../Cognition/README.md) - Handler 実装
- [../../../../tlaplus/](../../../../tlaplus/README.md) - TLA+ 仕様
