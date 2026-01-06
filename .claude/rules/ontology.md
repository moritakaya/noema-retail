# Noema: 圏論的定式化

## 1. 基本的枠組み

### 1.1 二つの圏

**Prop**（命題の圏）
- 対象: 論理命題
- 射: 含意 A → B
- 解釈: 認知可能な事実の空間

**Struct**（構造の圏）
- 対象: 命題＋意志の木構造
- 射: 構造を保存する変換
- 解釈: 意図の構造化された空間

### 1.2 随伴関手

$$\text{Intent} \dashv \text{Cognition}$$

```
Intent    : Prop → Struct
Cognition : Struct → Prop
```

自然同型：
$$\text{Hom}_{\text{Struct}}(\text{Intent}(P), S) \cong \text{Hom}_{\text{Prop}}(P, \text{Cognition}(S))$$

解釈：「意図 P を構造 S に到達させる道筋」と「構造 S を認知して P から理解する道筋」が自然に対応する。

### 1.3 Free-Forgetful 関係

この随伴は Free-Forgetful 型：
- **Intent（自由関手）**: 命題に自由な意志構造を付与
- **Cognition（忘却関手）**: 構造を忘却し命題に戻す

> **定式: 実行とは忘却である。**

## 2. 単位と余単位

### 2.1 単位 η

$$\eta : \text{Id}_{\text{Prop}} \Rightarrow \text{Cognition} \circ \text{Intent}$$

命題 P に対して η_P : P → Cognition(Intent(P))

解釈：純粋な命題が、意図として展開され、実行されて事実として戻る変換。「やってみなければ分からなかったこと」が η によって命題に折り返される。

### 2.2 余単位 ε

$$\varepsilon : \text{Intent} \circ \text{Cognition} \Rightarrow \text{Id}_{\text{Struct}}$$

構造 S に対して ε_S : Intent(Cognition(S)) → S

解釈：認知に基づいて意図し、その意図が構造に着地する。理解が行為となり、行為が構造に溶け込む。

## 3. モナドと Kleisli 圏

### 3.1 随伴から生じるモナド

$$T = \text{Cognition} \circ \text{Intent} : \text{Prop} \to \text{Prop}$$

- 単位: η : Id ⇒ T
- 乗法: μ : T² ⇒ T（余単位から導出）

### 3.2 Kleisli 射としてのプログラム

Kleisli 圏 Prop_T における射：

$$f : A \to T(B) = A \to \text{Cognition}(\text{Intent}(B))$$

解釈：「命題 A を前提として、B を意図し、それを認知可能な事実として回収する」

## 4. Vorzeichnungsschema

### 4.1 Freer Monad

生の操作 f : U に対して：

$$\text{Freer } f = \text{Free}(\text{Coyoneda } f)$$

ここで Coyoneda は左 Kan 拡張による自由関手構成：

$$\text{Coyoneda } f = \text{Lan}_Y f$$

### 4.2 Codensity 変換

Freer f に Codensity 変換を施す：

$$\text{Codensity}(\text{Freer } f)(A) = \forall R.\, (A \to \text{Freer } f\, R) \to \text{Freer } f\, R$$

この変換は：
- 左結合による非効率を解消
- 継続を通じた「解釈への志向性」を構造に埋め込む

### 4.3 Vorzeichnungsschema の定式化

$$\text{Vorzeichnung} = \text{Freer } f$$
$$\text{Vorzeichnung}^c = \text{Codensity}(\text{Freer } f)$$

## 5. Codensity Monad

### 5.1 右 Kan 拡張による定義

$$T^c = \text{Ran}_{\text{Cognition}} \text{Cognition}$$

### 5.2 Codensity の二重の役割

| 役割 | 表現 | 解釈 |
|---|---|---|
| 意味論的 | T^c = Ran_G G | 認知が意志を規定する |
| 構文論的 | Codensity(Freer f) | 意志が認知を予期する |

Vorzeichnungsschema はこの二つが交差する場所に位置する。

## 6. 分散システムへの応用

### 6.1 Vorzeichnungsschema の伝播

分散システムにおいて、ノード間で共有すべきは実行結果ではなく Vorzeichnungsschema である。

- 意志構造を保存したまま伝播
- 各ノードで独立に忘却（実行）可能
- 同一の Vorzeichnungsschema から異なる実行結果が生じうる

### 6.2 合成可能性

Freer Monad の Kleisli 合成により、Vorzeichnungsschema は合成可能：

$$g^* \circ f^* = (g^* \circ f)^*$$

### 6.3 遅延実行

Codensity 変換された Freer は継続ベース表現を持つ。これにより：

- 実行（忘却）のタイミングを制御可能
- 必要になるまで可能性を保存
- 投機的実行と確定的実行の区別を型レベルで表現

## 7. 最終定式

> **プログラムとは、主体が世界に対して投げかける意志を、Vorzeichnungsschema として構造化し、認知による忘却を通じて事実へと崩落させる、対話的運動である。**

> **Vorzeichnungsschema とは、Freer モナド（および、その Codensity 変換）として定式化される、認知を予描しつつ未だ認知に先立つ、意志の先験的形式である。**

> **実行とは忘却である。自由な構造は消え、可能性は一つの現実に押し潰される。**
