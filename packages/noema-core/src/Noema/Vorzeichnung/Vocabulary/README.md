# Vocabulary

## 役割

Vocabulary（語彙）は Intent が操作する対象の型を定義する。
AVDC（Subject, Thing, Relation, Contract）の4つの基本語彙と、それらの合成である NoemaF を提供する。

## 圏論的位置づけ

```
NoemaF = SubjectF ⊕ ThingF ⊕ RelationF ⊕ ContractF
       = Coproduct4

各語彙は操作の関手 f : Type → Type として定義される。
Intent f a b は f 上の Arrow として合成可能。
```

| 語彙 | 圏論的位置 | 操作対象 |
|------|-----------|---------|
| SubjectF | Base 圏 | 意志を持つ主体 |
| ThingF | Fiber 圏 | もの・こと（属性×位置×時間）|
| RelationF | Span 圏 | Subject-Thing 間の関係 |
| ContractF | 規定の圏 | 権利・義務、契約間関係 |

## 主要コンポーネント

- `SubjectF.purs`: 主体（契約当事者、Thing保持者、システムエージェント）
- `ThingF.purs`: 物（属性・位置・時間構造）
- `RelationF.purs`: 関係（所有、引当、代理、担保等）
- `ContractF.purs`: 契約（ライフサイクル、義務、契約間関係）
- `NoemaF.purs`: 上記4つの Coproduct

## ドメイン非依存設計

noema-core の Vocabulary はドメイン非依存。
小売固有の具体化は noema-retail で定義される。

| noema-core（抽象） | noema-retail（具体） |
|-------------------|---------------------|
| `RelationKind` (Json) | `RetailRelationKind` |
| `ChangeReason` (Json) | `RetailChangeReason` |
| `ChangeType` (String) | `RetailChangeType` |
| `SecurityType` (String) | `RetailSecurityType` |
| `AgencyScope` (String) | `RetailAgencyScope` |

### 変換パターン

```purescript
-- noema-retail での具体化
import Noema.Vorzeichnung.Vocabulary.RetailRelationKind

-- 具体 → 抽象
toRelationKind :: RetailRelationKind -> RelationKind
toRelationKind Owns = mkRelationKind "owns" "rights" Nothing

-- 抽象 → 具体（部分関数）
fromRelationKind :: RelationKind -> Maybe RetailRelationKind
fromRelationKind rk = case getRelationKindType rk of
  "owns" -> Just Owns
  _ -> Nothing
```

## RelationKind カテゴリ

関係の種別は以下のカテゴリに分類される：

| カテゴリ | 意味 | 例 |
|---------|------|-----|
| spatial | 空間的関係 | containment（包摂） |
| rights | 権利関係 | owns, possesses, claims |
| temporal | 時間的関係 | reserves, commits |
| transitive | 過渡的関係 | transports, consigns |
| structural | 構造的関係 | composed_of, bundled_with |
| cognitive | 認識的関係 | observation |
| performative | 行為的関係 | agency |
| negative | 消極的関係 | restriction |

## 使用例

```purescript
import Noema.Vorzeichnung.Vocabulary.NoemaF (NoemaF, NoemaIntent)
import Noema.Vorzeichnung.Vocabulary.ThingF (getProperty, getSitus)
import Noema.Vorzeichnung.Vocabulary.RelationF (containmentKind)

-- Thing の属性を取得する Intent
getPrice :: ThingId -> NoemaIntent Unit PropertyValue
getPrice tid = injectThingF $ getProperty tid (PropertyKey "price")
```

## 他のモジュールとの関係

```
Vocabulary/（操作の定義）
    │
    ▼ Intent で使用
Vorzeichnung/Intent.purs
    │
    ▼ Interpretation で解釈
noema-retail/Cognition/*Interpretation.purs
    │
    ▼ Factum として崩落
Sedimentation/Factum.purs
```
