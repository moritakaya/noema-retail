# Topos

## 役割

グロタンディーク・トポスとしての論理的空間の基盤を定義する。
意志（Intent）が展開され、沈殿（Sedimentation）により事実へと崩落する場。

## 圏論的位置づけ

```
Presheaf（前層）Set^{C^op}
    ↓ 層化関手 a
Sheaf（層）= Sedimentation の結果
```

| 概念 | 圏論 | 実装 |
|------|------|------|
| **Topos** | グロタンディーク・トポス Sh(C) | このディレクトリ全体 |
| **Situs** | Site C の対象（点） | DO の識別子 |
| **Nomos** | 被覆構造（Grothendieck topology） | 法の構造（本則 + 附則） |
| **World** | Site の特定の点における法的文脈 | (NomosVersion, region, timestamp) |
| **Presheaf** | 前層 Set^{C^op} | 懸濁環境 |
| **Connection** | 位相論的接続 | Nomos バージョン間の移行検証 |

## 主要コンポーネント

- `Situs.purs`: 空間座標（Site の点、DO の識別子）
- `Nomos.purs`: 法座標（被覆構造、附則、Connection）
- `Presheaf.purs`: 懸濁環境（層化前の状態）

## グロタンディーク構成との対応

```
┌─────────────────────────────────────────────────────────────┐
│                  グロタンディーク・トポス                    │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Site C（サイト）                                           │
│  ├── 対象: Subject（DO）← Situs で識別                     │
│  └── 被覆: Nomos（合法な操作の族）                          │
│                                                             │
│  Presheaf 圏 Set^{C^op}                                    │
│  ├── 対象: 前層 P: C^op → Set                              │
│  └── 懸濁環境として機能                                     │
│                                                             │
│  層化関手 a: Presheaf → Sheaf                              │
│  ├── Sedimentation により実現                               │
│  └── 前層から層への崩落                                     │
│                                                             │
│  Sheaf 圏 Sh(C)（トポス）                                  │
│  ├── 対象: 層（沈殿した事実）                               │
│  └── Attractor が保持                                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## Nomos の構造

Nomos は「本則」と「附則」から構成される。

```purescript
type Nomos =
  { version :: NomosVersion
  , rules :: Rules                    -- 本則（Lean4 で検証）
  , supplementary :: SupplementaryProvisions  -- 附則
  , predecessor :: Maybe NomosVersion
  }
```

### 本則（Rules）

```purescript
type Rules =
  { schemaVersion :: String     -- スキーマバージョン
  , constraints :: Array String -- 制約（SQL CHECK等）
  , validations :: Array String -- バリデーションルール
  }
```

将来は Lean4 で証明された規則の参照を保持。

### 附則（Supplementary Provisions）

実際の法律と同様、施行時期や既存契約への適用を規定。

```purescript
type SupplementaryProvisions =
  { effectiveFrom :: Timestamp           -- 施行日
  , existingContracts :: ContractTransition  -- 既存契約の扱い
  , gracePeriod :: Maybe Duration        -- 猶予期間
  , exceptions :: Array ExceptionRule    -- 例外規則
  }

data ContractTransition
  = PreserveOldLaw   -- 旧法維持（例: 消費税の経過措置）
  | MigrateToNewLaw  -- 新法適用（一定期間後）
  | CaseByCase       -- Connection で動的判定
```

## Connection（位相論的接続）

Nomos バージョン間の「連続的な平行移動」を検証する。

```
Nomos v1 ────────────────────▶ Nomos v2
          Connection(Flat)
```

### 三分類

| 分類 | 意味 | 例 |
|------|------|-----|
| Flat | 連続的移行可能 | ドキュメント修正、パフォーマンス改善 |
| Curved | 非連続、警告を伴う | 予約上限の変更、スキーマの追加 |
| Critical | 即時適用必須 | セキュリティパッチ、法令対応 |

```purescript
data ConnectionType
  = Flat               -- 平坦：連続的移行可能
  | Curved Reason      -- 湾曲：非連続、警告を伴う
  | Critical Reason    -- 臨界：即時適用必須

verifyConnection :: World -> World -> ConnectionType
```

## 判例（Case Law）

Noema には「エラー」という概念はない。
Cognition が正常に崩落しなかったケースは「判例」として記録される。

```purescript
data SuspensionOutcome
  = Sedimented SedimentId World  -- 正常に沈殿
  | Abandoned                     -- ユーザーによる取り消し
  | Rejected World Reason         -- 判例
```

判例は将来の Nomos 改訂（立法）に影響を与える。

## Thing と Nomos の関係

### Thing は Nomos 非認識

Thing 自体は Nomos/World を持たない。Subject が World を持ち、
Thing は Subject に包摂されることで暗黙的に World を継承する。

```
Subject (SubjectF)
├── has: SubjectId (= Thing の situs)
├── has: World (Nomos context)
└── contains: Thing (via RelationF Contains/Guards)
    └── Thing (ThingF)
        ├── has: ThingId
        ├── has: properties
        ├── has: situs :: SubjectId (包摂する Subject)
        └── Nomos 非認識（Subject 経由で継承）
```

### プロパティ変更と Nomos

Thing のプロパティ変更は Subject の Sedimentation に記録される。
バリデーションは Cognition 層で Subject の World に基づき実行。

```
1. Intent: SetProperty thingId propertyKey value
2. Cognition: Subject の World から PropertySchema を取得
3. Validation: PropertySchema に基づきバリデーション
4. Sedimentation: Subject の Sediment に記録（World 付き）
```

### PropertySchema（Nomos 拡張）

Nomos.Rules に PropertySchema を定義し、Thing プロパティの型制約を規定。

```purescript
data PropertyType
  = StringType
  | NumberType
  | BooleanType
  | EnumType (Array String)
  | JsonType

type PropertySchema = Map PropertyKey PropertyType
```

Connection 検証時、PropertySchema の互換性も検証：
- 新しい PropertyKey の追加 → Flat
- PropertyType の制限強化 → Curved
- 必須プロパティの追加 → Critical

## 哲学的基盤

### Situs（空間座標）

ラテン語で「位置」「状態」。Site の語源。
グロタンディーク・トポスにおける「点」に対応し、
DO の識別子として機能する。

### Nomos（法座標）

ギリシャ語で「法」「規範」「慣習」（νόμος）。
被覆構造として「どの操作が合法か」を規定し、
Sediment の解釈を決定する。

### World（世界）

```
World = (NomosVersion, region, timestamp)
```

DO は同じ Situs でも、異なる World にいることがある。
DO が眠って起きた時、Situs は同じだが World が変わりうる。

### Presheaf（前層）

まだ層化されていない状態。
意志（Intent）は Presheaf として構造化され、
Cognition を通じて層（Sheaf = 事実）へと崩落する。

## 使用例

```purescript
import Noema.Topos.Situs (SubjectId, ThingId, mkSubjectId, mkTimestamp)
import Noema.Topos.Nomos (NomosVersion(..), World, mkWorld, verifyConnection, ConnectionType(..))
import Noema.Topos.Presheaf (Presheaf, emptyPresheaf, suspend, complete, SuspensionOutcome(..))

-- Subject を識別
warehouseId :: SubjectId
warehouseId = mkSubjectId "warehouse-001"

-- 現在の World を取得
currentWorld :: World
currentWorld = mkWorld (NomosVersion "1.0.0") (mkTimestamp 1704067200000.0)

-- Presheaf に懸濁
suspendedPresheaf :: Presheaf
suspendedPresheaf = suspend warehouseId intentJson (emptyPresheaf suspensionId timestamp currentWorld)

-- Connection を検証
case verifyConnection targetWorld currentWorld of
  Flat -> -- 連続的に移行可能
  Curved reason -> -- 警告付きで移行（附則を参照）
  Critical reason -> -- 即時対応が必要
```

## 他のモジュールとの関係

```
Topos/
├── Situs.purs    ─────────────────────┐
├── Nomos.purs    ─────────────────────┼──► Vorzeichnung/Vocabulary/
└── Presheaf.purs ─────────────────────┘         │
                                                 ↓
                                          Cognition/Interpretation
                                                 │
                                                 ↓
                                          Sedimentation/Factum
                                                 │
                                                 ↓
                                          Sedimentation/Seal（World 記録）
```
