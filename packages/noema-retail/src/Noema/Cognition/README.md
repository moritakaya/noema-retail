# Cognition (noema-retail)

## 役割

Intent（意志構造）を Factum（流動的事実）へ解釈する Interpretation の実装。
Retail ドメインに特化した具体的な SQLite 操作への変換を行う。

## 圏論的位置づけ

- **関手**: Interpretation は自然変換 `f ~> Factum` として機能
- **A-algebra homomorphism**: 語彙 Functor を具体的実装へ写す
- **随伴関係**: Vorzeichnung ⊣ Cognition の右側

> **実行とは忘却である。**

## 主要コンポーネント

### 実装済み

| ファイル | 語彙 | 説明 |
|----------|------|------|
| `InventoryInterpretation.purs` | InventoryF | 在庫操作を SQLite へ解釈 |
| `SubjectInterpretation.purs` | SubjectF | 主体操作を SQLite へ解釈 |
| `ThingInterpretation.purs` | ThingF | 物操作を SQLite へ解釈（時間構造含む） |
| `RelationInterpretation.purs` | RelationF | 関係操作を SQLite へ解釈 |
| `StorageInterpretation.purs` | StorageF | 汎用ストレージ操作 |

| `ContractInterpretation.purs` | ContractF | 契約操作を SQLite へ解釈（ライフサイクル、義務、契約間関係） |

### 統合 Interpretation

| ファイル | 語彙 | 説明 |
|----------|------|------|
| `NoemaInterpretation.purs` | NoemaF | 4語彙を統合した Interpretation（余積の普遍性） |

## スキーマ設計原則

1. **Sediment のみ**: UPDATE 禁止、INSERT のみ（イベントソーシング）
2. **論理削除**: `removed_at` カラムで削除を表現
3. **World 記録**: 変更時点の法座標を記録
4. **外部キー**: Subject に帰属するデータは外部キーで参照

## 使用例

```purescript
-- 環境を作成
env <- recognize $ mkRelationEnv sql

-- Intent を実行
result <- runRelationIntent env (getRelationsFrom subjectId Owns) unit
-- result :: Factum (Array Relation)

-- エントリーポイントで Factum → Effect に変換
handleFetch req = collapse do
  result <- runRelationIntent env intent unit
  recognize $ jsonResponse result
```

## RelationInterpretation の SQLite スキーマ

```sql
-- 関係マスタ
CREATE TABLE relation (
  id TEXT PRIMARY KEY,
  kind TEXT NOT NULL,
  from_subject TEXT NOT NULL,
  to_thing TEXT NOT NULL,
  metadata TEXT,
  valid_from REAL NOT NULL,
  valid_until REAL,
  contract_ref TEXT,
  created_at REAL NOT NULL,
  removed_at REAL
);

-- 所有権移転ログ
CREATE TABLE ownership_transfer_log (
  id TEXT PRIMARY KEY,
  thing_id TEXT NOT NULL,
  from_subject TEXT NOT NULL,
  to_subject TEXT NOT NULL,
  via_subject TEXT,
  contract_ref TEXT NOT NULL,
  created_at REAL NOT NULL
);

-- 関係 Sediment ログ
CREATE TABLE relation_sediment (
  id TEXT PRIMARY KEY,
  relation_id TEXT NOT NULL,
  sequence_id INTEGER NOT NULL,
  operation TEXT NOT NULL,
  payload TEXT NOT NULL,
  created_at REAL NOT NULL
);
```

## 関係種別（RelationKind）

| カテゴリ | 種別 | 意味 |
|----------|------|------|
| 包摂 | Contains, Guards | 空間的な含有 |
| 権利 | Owns, Possesses, Claims, Secures, SharedBy | 法的関係 |
| 引当 | Reserves, Commits, Intends | 時間的確保 |
| 移動 | Transports, Consigns | 過渡的状態 |
| 構成 | ComposedOf, BundledWith, Substitutes | 構造的関係 |
| 観測 | Observes, Tracks | 認識的関係 |
| 代理 | ActsFor | 行為的関係 |
| 制限 | Restricts | 消極的関係 |

## ContractInterpretation の SQLite スキーマ

```sql
-- 契約マスタ
CREATE TABLE contract (
  id TEXT PRIMARY KEY,
  party_a TEXT NOT NULL,
  party_b TEXT NOT NULL,
  status TEXT NOT NULL DEFAULT 'Draft',
  nomos_ref TEXT,
  created_at REAL NOT NULL,
  updated_at REAL NOT NULL
);

-- 契約条項
CREATE TABLE contract_term (
  id TEXT PRIMARY KEY,
  contract_id TEXT NOT NULL,
  term_order INTEGER NOT NULL,
  term_content TEXT NOT NULL
);

-- 契約対象 Thing
CREATE TABLE contract_thing_ref (
  contract_id TEXT NOT NULL,
  thing_id TEXT NOT NULL,
  PRIMARY KEY (contract_id, thing_id)
);

-- 義務
CREATE TABLE obligation (
  id TEXT PRIMARY KEY,
  contract_id TEXT NOT NULL,
  kind TEXT NOT NULL,
  debtor TEXT NOT NULL,
  creditor TEXT NOT NULL,
  thing_ref TEXT,
  amount REAL,
  due_date REAL,
  status TEXT NOT NULL DEFAULT 'Pending',
  created_at REAL NOT NULL
);

-- 履行証明
CREATE TABLE fulfillment_proof (
  id TEXT PRIMARY KEY,
  obligation_id TEXT NOT NULL,
  evidence TEXT NOT NULL,
  created_at REAL NOT NULL
);

-- 契約間関係
CREATE TABLE contract_relation (
  id TEXT PRIMARY KEY,
  from_contract TEXT NOT NULL,
  to_contract TEXT NOT NULL,
  kind TEXT NOT NULL,
  description TEXT,
  created_at REAL NOT NULL
);
```

## 契約間関係（ContractRelationKind）

| 種別 | 意味 |
|------|------|
| Prerequisite | 前提（B は A がないと成立しない） |
| Subordinate | 従属（A 終了で B も終了） |
| Consideration | 対価（A の履行が B の対価） |
| Security | 担保（B は A の履行を担保） |
| Amendment | 変更（B は A を変更） |
| Termination | 解除（B は A を解除） |
