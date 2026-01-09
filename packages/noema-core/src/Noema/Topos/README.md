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
| **Nomos** | 被覆構造（Grothendieck topology） | Nomos のバージョン |
| **Presheaf** | 前層 Set^{C^op} | ステージング環境 |

## 主要コンポーネント

- `Situs.purs`: 空間座標（Site の点、DO の識別子）
- `Nomos.purs`: 法座標（被覆構造、合法性の規定）
- `Presheaf.purs`: ステージング環境（層化前の状態）

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
│  └── ステージング環境として機能                             │
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

## 哲学的基盤

### Situs（空間座標）

ラテン語で「位置」「状態」。Site の語源。
グロタンディーク・トポスにおける「点」に対応し、
DO の識別子として機能する。

### Nomos（法座標）

ギリシャ語で「法」「規範」「慣習」（νόμος）。
被覆構造として「どの操作が合法か」を規定し、
Sediment の解釈を決定する。

### Presheaf（前層）

まだ層化されていない状態。
意志（Intent）は Presheaf として構造化され、
Cognition を通じて層（Sheaf = 事実）へと崩落する。

## 使用例

```purescript
import Noema.Topos.Situs (SubjectId, ThingId, mkSubjectId)
import Noema.Topos.Nomos (NomosVersion, World, mkWorld)
import Noema.Topos.Presheaf (Presheaf, emptyPresheaf, stage, commit)

-- Subject を識別
warehouseId :: SubjectId
warehouseId = mkSubjectId "warehouse-001"

-- 現在の World を取得
currentWorld :: World
currentWorld = mkWorld (NomosVersion "1.0.0") timestamp

-- Presheaf にステージング
stagedPresheaf :: Presheaf
stagedPresheaf = stage warehouseId intentJson (emptyPresheaf stagingId timestamp)
```

## 他のモジュールとの関係

```
Topos/
├── Situs.purs    ─────────────────────┐
├── Nomos.purs    ─────────────────────┼──► Vorzeichnung/Vocabulary/
└── Presheaf.purs ─────────────────────┘         │
                                                 ↓
                                          Cognition/Handler
                                                 │
                                                 ↓
                                          Sedimentation/Attractor
```
