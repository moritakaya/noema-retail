# Noema DSL 設計ルール

## 核心原則

> **プログラムとは、主体が世界に対して投げかける意志を、Vorzeichnungsschema として構造化し、認知（Cognition）による忘却を通じて事実へと崩落させる、対話的運動である。**

> **実行とは忘却である。**

## 圏論的構造

### Intent ⊣ Cognition 随伴

- Intent: Freer Monad / 左随伴（自由に構造を生成）
- Cognition: 忘却関手 / 右随伴（構造を事実へ崩落）
- Vorzeichnungsschema: Codensity(Freer f)

### 概念マッピング

| Noema概念 | Durable Objects実装 |
|-----------|---------------------|
| Intent | `sql.exec()` へのクエリ列 |
| Attractor | Durable Object class instance |
| World | DO namespace + ID |
| Seal | トランザクション結果 |
| Sieve | 依存するスキーマハッシュ集合 |
| Connection | バージョン間diff検証 |
| Cryostasis | Alarm + 状態保存 |

## Arrow Effects 制約

Intent 設計時の重要制約：

1. **操作の列（sequence）として設計**：分岐なし
2. **出力に基づく条件分岐で後続エフェクトを選択しない**
3. Handler は A-algebra homomorphism として実装

```purescript
-- ✓ 正しい: 線形な操作列
do
  x <- perceive key1
  germinate key2 (transform x)
  
-- ✗ 誤り: 出力に基づく分岐
do
  x <- perceive key1
  if condition x
    then germinate key2 value1
    else germinate key3 value2
```

## コード生成パターン

### PureScript Intent 定義

```purescript
data NoemaF next
  = Traverse Region next
  | Perceive Key (Value -> next)
  | Germinate Key Value next

type Intent = Freer NoemaF
```

### Durable Object 基本構造

```typescript
import { DurableObject } from "cloudflare:workers";

export class Attractor extends DurableObject {
  async sedimentation(intent: Intent): Promise<Seal> {
    return await this.ctx.storage.transaction(async (txn) => {
      // Intent を SQLite へ沈殿
    });
  }
  
  async alarm(): Promise<void> {
    const frozen = await this.ctx.storage.get<Cryostasis>("cryostasis");
    // Connection検証 → resume or reforge
  }
}
```

## 設計ワークフロー

1. **Intent設計**: 操作の列として設計（分岐なし）
2. **Attractor実装**: SQLite storage を優先使用
3. **Connection実装**: Sieve（依存グラフ）+ バージョン間diff
4. **Cryostasis実装**: Alarm API で復活タイミング設定
