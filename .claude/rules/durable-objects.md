# Durable Objects 実装パターン

Noema DSL を Cloudflare Durable Objects 上に実装する際のパターン集。

## 概念マッピング

| Noema概念 | Durable Objects実装 |
|-----------|---------------------|
| **Intent** | `sql.exec()` へのクエリ列 |
| **Attractor** | Durable Object class instance |
| **World** | DO namespace + ID |
| **Nomos** | スキーマ + 制約 |
| **Seal** | トランザクション結果 |
| **Sieve** | 依存するスキーマハッシュ集合 |
| **Connection** | バージョン間diff検証 |
| **Cryostasis** | Alarm + 状態保存 |

## 基本構造

### Attractor（Durable Object）

```typescript
import { DurableObject } from "cloudflare:workers";

export class Attractor extends DurableObject<Env> {
  private sql: SqlStorage;

  constructor(ctx: DurableObjectState, env: Env) {
    super(ctx, env);
    this.sql = ctx.storage.sql;
  }

  // 状態の沈殿（Intent → Seal）
  async sedimentation(intent: Intent): Promise<Seal> {
    return await this.ctx.storage.transaction(async (txn) => {
      // Intent を SQLite へ沈殿
      for (const op of intent.operations) {
        this.sql.exec(op.query, ...op.params);
      }
      return { success: true, timestamp: Date.now() };
    });
  }
  
  // 復活の儀式（Cryostasis → Resume/Reforge）
  async alarm(): Promise<void> {
    const frozen = await this.ctx.storage.get<Cryostasis>("cryostasis");
    if (!frozen) return;
    
    // Connection検証
    const isFlat = await this.verifyConnection(frozen.nomosHash);
    if (isFlat) {
      await this.resume(frozen);
    } else {
      await this.reforge(frozen);
    }
  }
}
```

### Storage API パターン

```typescript
// SQLite Storage（推奨）
this.sql.exec(`
  CREATE TABLE IF NOT EXISTS inventory (
    product_id TEXT PRIMARY KEY,
    quantity INTEGER NOT NULL,
    updated_at TEXT NOT NULL
  )
`);

// Key-Value Storage
await this.ctx.storage.put("key", value);
const value = await this.ctx.storage.get<Type>("key");

// トランザクション
await this.ctx.storage.transaction(async (txn) => {
  // 複数操作をアトミックに
});
```

### Alarm（Cryostasis 実装）

```typescript
// 復活タイミングを設定
await this.ctx.storage.setAlarm(Date.now() + 60000); // 1分後

// Cryostasis 状態を保存
await this.ctx.storage.put("cryostasis", {
  state: currentState,
  nomosHash: schema.hash(),
  sieve: dependencies
});
```

## 設計ワークフロー

### 1. Intent設計時

1. 操作の列（sequence）として設計（分岐なし）
2. Arrow制約を意識：出力に基づく条件分岐で後続エフェクトを選択しない
3. Handler で解釈を与える

### 2. Attractor（DO）実装時

1. SQLite storage（`sql.exec`）を優先使用
2. トランザクション境界を明確に
3. 状態変更は必ずログに記録（Event Sourcing）

### 3. Connection（整合性検証）実装時

1. Sieve（依存グラフ）の設計
2. バージョン間diffの計算方法
3. Flat/Curved判定ロジック

### 4. Cryostasis（待機/復活）実装時

1. Alarm APIで復活タイミングを設定
2. 状態 + nomosHash + sieveを保存
3. 復活時のreforge処理

## wrangler.json 設定

```json
{
  "durable_objects": {
    "bindings": [
      {
        "name": "INVENTORY_ATTRACTOR",
        "class_name": "InventoryAttractor"
      }
    ]
  },
  "migrations": [
    {
      "tag": "v1",
      "new_sqlite_classes": ["InventoryAttractor"]
    }
  ]
}
```

## Worker からの呼び出し

```typescript
// Durable Object ID を取得
const id = env.INVENTORY_ATTRACTOR.idFromName(productId);

// Stub を取得
const stub = env.INVENTORY_ATTRACTOR.get(id);

// RPC 呼び出し
const result = await stub.sedimentation(intent);
```
