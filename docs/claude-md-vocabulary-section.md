# Vocabulary 設計ガイド（CLAUDE.md 追加セクション）

## Vocabulary の哲学的基盤

### 存在論的三層

```
Nomos（大域意志）: 法律、商習慣 → Sediment の解釈を規定
Subject（主体）: 意志を持つ → DO として実装
Thing（物）: 意志を持たない → Subject に包摂される
```

### グロタンディーク構成

```
Locus = 空間座標（DO の ID）
World = 法座標（Nomos のバージョン）

Base 圏: DO のネットワーク（水平射 = RPC）
Fiber 圏: DO 内の状態空間（垂直射 = Sediment）
```

### Thing = Subject の包摂

Thing 自体は DO ではない。Subject が Thing を「包摂」する。
- Thing の同一性 = 包摂する Subject の id
- Thing の状態 = Sediment の積分値

## 四つの語彙

```purescript
type NoemaF = Coproduct4 SubjectF ThingF RelationF ContractF
```

| 語彙 | 圏論的位置 | 操作対象 |
|------|-----------|---------|
| SubjectF | Base 圏 | 意志を持つ主体 |
| ThingF | Fiber 圏 | もの・こと（属性×位置×時間）|
| RelationF | Span 圏 | Subject-Thing 間の関係 |
| ContractF | 規定の圏 | 権利・義務、契約間関係 |

## ThingF の時間構造（Husserl）

```
Retention（把持）: 過去の Snapshot
Primal（原印象）: 現在の状態
Protention（予持）: 未来の Pending Intent
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

## 実装規則

1. **Sediment のみ**: UPDATE 禁止、INSERT のみ
2. **Arrow 維持**: ArrowChoice 禁止、分岐は Handler で
3. **Source of Truth**: 所有権等は Thing を包摂する Subject が保持
4. **View**: Container の Contents はキャッシュ
