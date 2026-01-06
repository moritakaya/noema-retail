# Noema: プログラムの圏論的存在論

## 核心命題

> **プログラムとは、主体が世界に対して投げかける意志（Intent）を、Vorzeichnungsschema として構造化し、認知（Cognition）による忘却を通じて事実へと崩落させる、対話的運動である。**

> **実行とは忘却である。**

## 基本構造

### 随伴 Intent ⊣ Cognition

```
Intent    : Prop → Struct    （左随伴・自由関手）
Cognition : Struct → Prop    （右随伴・忘却関手）
```

| 圏 | 対象 | 解釈 |
|---|---|---|
| **Prop** | 論理命題 | 認知可能な事実の空間 |
| **Struct** | 命題＋意志の木構造 | 意図の構造化された空間 |

この随伴は Free-Forgetful 関係を表す：
- **Intent**: 命題から意志の構造を自由に生成する
- **Cognition**: 構造を忘却し、事実に落とし込む

### 三層構造

| 層 | 構造 | 解釈 |
|---|---|---|
| 原初的意志 | 型構成子 f | 構造化されていない意図の断片 |
| Vorzeichnungsschema | Freer f / Codensity(Freer f) | 認知を予期して構造化された意志 |
| 実行結果 | Cognition による解釈 | 構造が忘却され事実に崩落した状態 |

## Vorzeichnungsschema

### 定義

```
Vorzeichnung = Freer f = Free(Coyoneda f)
Vorzeichnung^c = Codensity(Freer f)
```

Vorzeichnungsschema（予描図式）は：
- まだ実行（忘却）されていない純粋な意志構造
- 認知されることを予期しつつ、未だ認知に先立つ
- 可能性の樹形図として分岐を保存している

### なぜ Free ではなく Freer か

| 概念 | Free | Freer |
|---|---|---|
| 前提 | F が関手 | F は任意の型構成子 |
| 含意 | 意志は整った形で生起 | 意志は生の操作として生起し、認知により整列 |

意志は関手として整った形では生起しない。Freer は「まだ整っていない意図が構造化される過程」を含む。

## 設計原則への応用

Noema DSL を設計・実装する際：

1. **コードは Freer 構造として扱う**: 実行前の意志構造を保存
2. **実行は忘却として設計する**: 構造から事実への崩落を明示的にモデル化
3. **分散システムでは Vorzeichnungsschema を共有する**: 実行結果ではなく意志構造を伝播
