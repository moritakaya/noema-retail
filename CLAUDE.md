# Noema Retail Backend

## プロジェクト概要

小売業基幹システムのための DSL 実装。Cloudflare Workers + Durable Objects 上で動作する分散システム。

## 哲学的基盤

> **プログラムとは、主体が世界に対して投げかける意志を、Vorzeichnungsschema として構造化し、認知（Cognition）による忘却を通じて事実へと崩落させる、対話的運動である。**

> **実行とは忘却である。**

## 圏論的構造

```
Intent (Freer RetailF)
      │
      ├──► SubjectF   → Subject 圏（契約主体）
      ├──► ThingF     → Thing 圏（物）  
      ├──► ContextF   → Context 圏（時空間）
      └──► InventoryF → Inventory 圏（在庫）
```

### 核心定式

- **Intent ⊣ Cognition 随伴**: 意志と認知の対
- **Freer Monad**: 効果の分離と合成
- **Presheaf**: `Inventory : Channel^op → Set`

## 技術スタック

| 層 | 技術 | 役割 |
|---|---|---|
| DSL | PureScript | 意図の記述（Freer InventoryF） |
| Runtime | TypeScript | Cloudflare Workers 実装 |
| State | Durable Objects + SQLite | 状態管理（Attractor） |
| Gateway | Hono | ルーティング |

## ディレクトリ構造

```
noema-retail/
├── src/domain/          # PureScript DSL
│   └── Inventory.purs
├── workers/             # TypeScript Workers
│   ├── index.ts         # エントリーポイント
│   ├── attractors/      # Durable Objects
│   └── adapters/        # チャネル連携
├── docs/                # 設計ドキュメント
├── .claude/rules/       # Claude Code ルール
├── wrangler.json        # Cloudflare 設定
└── CLAUDE.md            # このファイル
```

## コマンド

```bash
# 開発
npm install
wrangler dev

# デプロイ
wrangler deploy

# 本番デプロイ
wrangler deploy --env production
```

## 設計原則

1. **Single Source of Truth**: Noema が在庫の真実
2. **Event Sourcing**: 全変更を `inventory_log` に記録
3. **Eventual Consistency**: チャネル同期は非同期（5分毎 Cron）
4. **Handler Pattern**: Arrow Effects に基づく効果分離

## 参照

- `docs/inventory-sync-architecture.md`: 在庫連携アーキテクチャ
- `.claude/rules/`: プロジェクト固有のルール
