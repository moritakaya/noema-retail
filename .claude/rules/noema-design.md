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
| **Interpretation** | 自然変換 f ~> Factum |
| **Factum** | 流動的事実（Effect ラッパー） |
| Attractor | Durable Object class instance |
| World | (NomosVersion, region, timestamp) |
| **Nomos** | 本則 + 附則（経過措置） |
| **Connection** | Flat / Curved / Critical |
| Seal | トランザクション結果 + World |
| Sieve | 依存するスキーマハッシュ集合 |
| Cryostasis | Alarm + 状態保存 |
| **判例** | StagingOutcome.Rejected |

## Nomos（法の構造）

### 本則 + 附則

```purescript
type Nomos =
  { version :: NomosVersion
  , rules :: Rules                    -- 本則（Lean4 で検証）
  , supplementary :: SupplementaryProvisions  -- 附則
  , predecessor :: Maybe NomosVersion
  }
```

### 附則（経過措置）

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
  | MigrateToNewLaw  -- 新法適用
  | CaseByCase       -- Connection で動的判定
```

## Connection（位相論的接続）

Nomos バージョン間の「連続的な平行移動」を検証する。

### 三分類

| 分類 | 意味 | 例 |
|------|------|-----|
| Flat | 連続的移行可能 | ドキュメント修正、パフォーマンス改善 |
| Curved | 非連続、警告を伴う | 予約上限の変更、スキーマの追加 |
| Critical | 即時適用必須 | セキュリティパッチ、法令対応 |

```purescript
data ConnectionType
  = Flat               -- 平坦
  | Curved Reason      -- 湾曲
  | Critical Reason    -- 臨界

verifyConnection :: World -> World -> ConnectionType
```

## 判例（Case Law）

Noema には「エラー」という概念はない。
Cognition が正常に崩落しなかったケースは「判例」として記録される。

```purescript
data StagingOutcome
  = Sedimented SedimentId World  -- 正常に沈殿
  | Abandoned                     -- ユーザーによる取り消し
  | Rejected World Reason         -- 判例
```

判例は将来の Nomos 改訂（立法）に影響を与える。

## Arrow Effects 制約

Intent 設計時の重要制約：

1. **操作の列（sequence）として設計**：分岐なし
2. **出力に基づく条件分岐で後続エフェクトを選択しない**
3. Interpretation は A-algebra homomorphism として実装
4. **FFI 境界**: `recognize` で Effect → Factum、`collapse` で Factum → Effect

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

## Factum と Effect の境界

```purescript
-- Factum: 内部の事実
newtype Factum a = Factum (Effect a)

-- collapse: 外界への忘却
handleFetch :: Request -> Effect Response
handleFetch req = collapse do
  result <- runInventoryIntent env intent unit
  recognize $ jsonResponse result

-- recognize: 外界からの認識
now <- recognize currentTimestamp
```

## Seal と World

Seal には沈殿時の World が記録される。

```purescript
newtype Seal = Seal
  { success :: Boolean
  , sedimentId :: SedimentId
  , hash :: String
  , timestamp :: Timestamp
  , world :: World             -- 適用された法
  }
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
      // Seal に現在の World を記録
    });
  }

  async alarm(): Promise<void> {
    const frozen = await this.ctx.storage.get<Cryostasis>("cryostasis");
    // Connection 検証 → Flat なら resume、Curved なら附則参照
  }
}
```

## 設計ワークフロー

1. **Intent設計**: 操作の列として設計（分岐なし）
2. **Attractor実装**: SQLite storage を優先使用
3. **Connection実装**: Flat / Curved / Critical の判定
4. **附則設計**: 経過措置、既存契約の扱い
5. **Cryostasis実装**: Alarm API で復活タイミング設定
