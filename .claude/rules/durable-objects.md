# Durable Objects 実装パターン

Noema DSL を Cloudflare Durable Objects 上に実装する際のパターン集。

## 概念マッピング

| Noema概念 | Durable Objects実装 |
|-----------|---------------------|
| **Intent** | `sql.exec()` へのクエリ列 |
| **Interpretation** | 自然変換 f ~> Factum |
| **Factum** | 流動的事実（Effect ラッパー） |
| **Attractor** | Durable Object class instance |
| **World** | (NomosVersion, region, timestamp) |
| **Nomos** | 本則 + 附則（Rules + SupplementaryProvisions） |
| **Connection** | Flat / Curved / Critical |
| **Seal** | トランザクション結果 + World |
| **Sieve** | 依存するスキーマハッシュ集合 |
| **Cryostasis** | Alarm + 状態保存 |
| **判例** | StagingOutcome.Rejected |

## 基本構造

### Attractor（Durable Object）

```typescript
import { DurableObject } from "cloudflare:workers";

export class Attractor extends DurableObject<Env> {
  private sql: SqlStorage;
  private currentWorld: World;

  constructor(ctx: DurableObjectState, env: Env) {
    super(ctx, env);
    this.sql = ctx.storage.sql;
    this.currentWorld = {
      nomosVersion: env.NOMOS_VERSION,
      region: env.REGION,
      timestamp: Date.now()
    };
  }

  // 状態の沈殿（Intent → Seal）
  async sedimentation(intent: Intent, targetWorld: World): Promise<Seal> {
    // Connection を検証
    const connection = this.verifyConnection(targetWorld, this.currentWorld);

    switch (connection.type) {
      case "Flat":
        // 連続的移行可能：そのまま実行
        return await this.sedimentWithWorld(intent, this.currentWorld);

      case "Curved":
        // 非連続：附則を参照して処理
        const provisions = await this.getSupplementaryProvisions();
        return await this.sedimentWithProvisions(intent, provisions, connection.reason);

      case "Critical":
        // 即時適用必須：Intent を棄却し判例として記録
        return {
          success: false,
          world: this.currentWorld,
          reason: connection.reason,
          isCaseLaw: true  // 判例
        };
    }
  }

  // Connection を検証
  private verifyConnection(target: World, current: World): ConnectionResult {
    if (target.nomosVersion === current.nomosVersion) {
      return { type: "Flat" };
    }

    // 将来は Lean4 サービスと連携して判定
    return {
      type: "Curved",
      reason: "Version mismatch (pending Lean4 verification)"
    };
  }

  // 復活の儀式（Cryostasis → Resume/Reforge）
  async alarm(): Promise<void> {
    const frozen = await this.ctx.storage.get<Cryostasis>("cryostasis");
    if (!frozen) return;

    // Connection 検証
    const connection = this.verifyConnection(frozen.world, this.currentWorld);

    switch (connection.type) {
      case "Flat":
        await this.resume(frozen);
        break;
      case "Curved":
        // 附則に従って reforge
        const provisions = await this.getSupplementaryProvisions();
        await this.reforgeWithProvisions(frozen, provisions);
        break;
      case "Critical":
        // 即時対応が必要 - ログに記録
        await this.logCriticalConnection(frozen, connection.reason);
        break;
    }
  }
}
```

### Seal と World

```typescript
interface Seal {
  success: boolean;
  sedimentId: number;        // Lamport Clock
  hash: string;
  timestamp: number;
  world: World;              // 適用された法（重要！）
}

interface World {
  nomosVersion: string;
  region?: string;
  timestamp: number;
}
```

### Connection 型

```typescript
type ConnectionType = "Flat" | "Curved" | "Critical";

interface ConnectionResult {
  type: ConnectionType;
  reason?: string;
}

// Flat: 連続的移行可能（ドキュメント修正、パフォーマンス改善）
// Curved: 非連続、警告を伴う（予約上限の変更、スキーマの追加）
// Critical: 即時適用必須（セキュリティパッチ、法令対応）
```

### 附則（経過措置）の処理

```typescript
interface SupplementaryProvisions {
  effectiveFrom: number;     // 施行日
  existingContracts: ContractTransition;
  gracePeriod?: number;      // 猶予期間（ミリ秒）
  exceptions: ExceptionRule[];
}

type ContractTransition =
  | "PreserveOldLaw"   // 旧法維持
  | "MigrateToNewLaw"  // 新法適用
  | "CaseByCase";      // 動的判定

// 附則に従った沈殿
async sedimentWithProvisions(
  intent: Intent,
  provisions: SupplementaryProvisions,
  reason: string
): Promise<Seal> {
  const now = Date.now();

  // 猶予期間内か確認
  if (provisions.gracePeriod && now < provisions.effectiveFrom + provisions.gracePeriod) {
    // 旧法で処理
    return await this.sedimentWithOldLaw(intent);
  }

  switch (provisions.existingContracts) {
    case "PreserveOldLaw":
      return await this.sedimentWithOldLaw(intent);
    case "MigrateToNewLaw":
      return await this.sedimentWithWorld(intent, this.currentWorld);
    case "CaseByCase":
      // 個別判定が必要
      return await this.sedimentCaseByCase(intent, reason);
  }
}
```

## Storage API パターン

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
  world: this.currentWorld,  // World を記録
  sieve: dependencies
});
```

## 設計ワークフロー

### 1. Intent設計時

1. 操作の列（sequence）として設計（分岐なし）
2. Arrow制約を意識：出力に基づく条件分岐で後続エフェクトを選択しない
3. Interpretation で解釈を与え、Factum に崩落させる

### 2. Attractor（DO）実装時

1. SQLite storage（`sql.exec`）を優先使用
2. トランザクション境界を明確に
3. 状態変更は必ずログに記録（Event Sourcing）
4. **Seal に World を記録**

### 3. Connection（整合性検証）実装時

1. **三分類**: Flat / Curved / Critical
2. Flat: そのまま実行
3. Curved: 附則を参照
4. Critical: 判例として記録

### 4. 附則設計時

1. effectiveFrom（施行日）
2. existingContracts（既存契約の扱い）
3. gracePeriod（猶予期間）
4. exceptions（例外規則）

### 5. Cryostasis（待機/復活）実装時

1. Alarm APIで復活タイミングを設定
2. 状態 + World + sieveを保存
3. 復活時にConnection検証

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

// 現在の World を取得
const targetWorld = {
  nomosVersion: env.NOMOS_VERSION,
  region: env.REGION,
  timestamp: Date.now()
};

// RPC 呼び出し（targetWorld を渡す）
const result = await stub.sedimentation(intent, targetWorld);
```
