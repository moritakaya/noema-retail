# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## プロジェクト概要

小売業基幹システムのための DSL 実装。Cloudflare Workers + Durable Objects 上で動作する分散システム。

## 哲学的基盤

> **プログラムとは、主体が世界に対して投げかける意志を、Vorzeichnungsschema として構造化し、認知（Cognition）による忘却を通じて事実へと崩落させる、対話的運動である。**

> **実行とは忘却である。**

## コマンド

```bash
# 開発サーバー起動
npm run dev              # wrangler dev

# 型チェック・リント
npm run typecheck        # TypeScript型検査
npm run lint             # ESLint (workers/)

# テスト
npm run test             # Vitest 全テスト実行

# デプロイ
npm run deploy           # ステージング
npm run deploy:prod      # 本番
```

## 技術スタック

| 層 | 技術 | 役割 |
|---|---|---|
| DSL | PureScript | 意図の記述（Freer InventoryF） |
| Runtime | TypeScript | Cloudflare Workers 実装 |
| State | Durable Objects + SQLite | 状態管理（Attractor） |
| Gateway | Hono | ルーティング |
| Payment | Stripe | 決済処理 |

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

## アーキテクチャ

### Attractor（Durable Objects）

`workers/attractors/InventoryAttractor.ts` が中核。SQLite で以下を管理:
- `inventory`: 商品在庫（sku, location_id, quantity）
- `inventory_log`: イベントソーシング（sale, purchase, adjust, transfer, reserve, release, return）
- `channel_sync`: チャネル同期状態
- `reservation`: 予約在庫（TTL付き）

### チャネル連携

`workers/adapters/` 配下。各チャネル（Rakuten, Yahoo, Smaregi）との双方向同期:
- 5分毎の Cron で `scheduled()` が発火
- Webhook 受信で即時反映

### Arrow Effects 制約

Intent 設計時の重要制約（`.claude/rules/noema-design.md` 参照）:
1. 操作は**列（sequence）として設計**：分岐なし
2. 出力に基づく条件分岐で後続エフェクトを選択しない
3. Handler は A-algebra homomorphism として実装

```purescript
-- ✓ 正しい: 線形な操作列
do
  x <- perceive key1
  germinate key2 (transform x)

-- ✗ 誤り: 出力に基づく分岐
do
  x <- perceive key1
  if condition x then germinate key2 value1 else germinate key3 value2
```

## 設計原則

1. **Single Source of Truth**: Noema が在庫の真実
2. **Event Sourcing**: 全変更を `inventory_log` に記録
3. **Eventual Consistency**: チャネル同期は非同期（5分毎 Cron）
4. **Handler Pattern**: Arrow Effects に基づく効果分離

## シークレット管理

```bash
wrangler secret put SMAREGI_ACCESS_TOKEN
wrangler secret put RAKUTEN_SERVICE_SECRET
wrangler secret put YAHOO_ACCESS_TOKEN
wrangler secret put STRIPE_SECRET_KEY
wrangler secret put STRIPE_WEBHOOK_SECRET
```

## 参照

- `docs/inventory-sync-architecture.md`: 在庫連携アーキテクチャ詳細
- `.claude/rules/noema-design.md`: Noema DSL 設計ルール

## 言語
日本語で応答してください。
