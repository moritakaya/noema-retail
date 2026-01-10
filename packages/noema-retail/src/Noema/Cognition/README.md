# Cognition (noema-retail)

## 役割

Intent（意志構造）を Factum（流動的事実）へ解釈する Interpretation の実装。
Retail ドメインに特化した具体的な SQLite 操作への変換を行う。

## 圏論的位置づけ

- **関手**: Interpretation は自然変換 `f ~> Factum` として機能
- **A-algebra homomorphism**: 語彙 Functor を具体的実装へ写す
- **随伴関係**: Vorzeichnung ⊣ Cognition の右側

> **実行とは忘却である。**

### Augmented Virtual Double Category (AVDC)

Noema DSL は AVDC（拡張仮想二重圏）として構造化されている。

```
                    水平射（RPC）
     ┌────────────────────────────────────┐
     │                                    │
     │   SubjectA ─────RPC────▶ SubjectB  │  ← Base 圏
     │      │                      │      │    （DO ネットワーク）
     │      │                      │      │
     │  Sediment               Sediment   │  ← 垂直射
     │      │                      │      │    （状態遷移）
     │      ▼                      ▼      │
     │   State_n             State_m      │  ← Fiber 圏
     │                                    │    （DO 内部状態）
     └────────────────────────────────────┘
```

#### 二重圏の構成要素

| 構成要素 | Noema における実体 | 役割 |
|----------|-------------------|------|
| **0-cell** | Durable Object インスタンス | Subject（意志を持つ主体） |
| **水平射** | RPC / SendIntent | Subject 間通信 |
| **垂直射** | Sediment（INSERT のみ） | 状態遷移（イベントソーシング） |
| **2-cell** | Intent の解釈結果 | 水平と垂直の整合性 |

#### Grothendieck 構成

```
π : E → B （射影関手）

E（全体圏）= Σ_{s ∈ B} Fiber(s)
B（基底圏）= Subject ネットワーク

Fiber(Subject_i) = その Subject 内の状態空間
```

- **Base 圏**: Subject（DO）のネットワーク。水平射は RPC。
- **Fiber 圏**: 各 Subject 内の状態空間。垂直射は Sediment。
- **全体圏**: Base と Fiber の Grothendieck 構成。

#### 射の合成

```
水平合成: SubjectA →(RPC)→ SubjectB →(RPC)→ SubjectC
垂直合成: State_0 →(Sed)→ State_1 →(Sed)→ State_2
交換法則: 水平 ∘ 垂直 = 垂直 ∘ 水平（分散トランザクションの整合性）
```

#### NoemaF と AVDC

```
NoemaF = SubjectF + ThingF + RelationF + ContractF（余積）

SubjectF  → 水平射の生成（SendIntent, ConfirmReceipt）
ThingF    → 垂直射の生成（SetProperty, RecordSitusChange）
RelationF → 2-cell の生成（Subject-Thing 間の関係）
ContractF → 法的整合性（Nomos による制約）
```

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

-- Intent を実現（realize）
result <- realizeRelationIntent env (getRelationsFrom subjectId Owns) unit
-- result :: Factum (Array Relation)

-- エントリーポイントで Factum → Effect に変換
handleFetch req = collapse do
  result <- realizeRelationIntent env intent unit
  recognize $ jsonResponse result
```

## SubjectInterpretation の SQLite スキーマ

```sql
-- 主体（意志を持つ存在）
CREATE TABLE subject (
  id TEXT PRIMARY KEY,
  kind TEXT NOT NULL,
  nomos_version TEXT NOT NULL,
  region TEXT,
  world_timestamp REAL NOT NULL,
  last_activity REAL NOT NULL,
  created_at REAL NOT NULL
);

-- 主体イベントログ
CREATE TABLE subject_log (
  id TEXT PRIMARY KEY,
  subject_id TEXT NOT NULL,
  event_type TEXT NOT NULL,
  payload TEXT,
  created_at REAL NOT NULL,
  FOREIGN KEY (subject_id) REFERENCES subject(id)
);
```

## ThingInterpretation の SQLite スキーマ

```sql
-- 物（Subject に包摂される）
CREATE TABLE thing (
  id TEXT PRIMARY KEY,
  situs TEXT NOT NULL,
  last_modified REAL NOT NULL,
  created_at REAL NOT NULL,
  FOREIGN KEY (situs) REFERENCES subject(id)
);

-- 物の属性（PropertyKey → PropertyValue）
CREATE TABLE thing_property (
  thing_id TEXT NOT NULL,
  property_key TEXT NOT NULL,
  property_value TEXT NOT NULL,
  updated_at REAL NOT NULL,
  PRIMARY KEY (thing_id, property_key),
  FOREIGN KEY (thing_id) REFERENCES thing(id)
);

-- Thing Sediment ログ（INSERT のみ、UPDATE 禁止）
CREATE TABLE thing_sediment (
  id TEXT PRIMARY KEY,
  thing_id TEXT NOT NULL,
  sequence_id INTEGER NOT NULL,
  intent_type TEXT NOT NULL,
  payload TEXT NOT NULL,
  created_at REAL NOT NULL,
  FOREIGN KEY (thing_id) REFERENCES thing(id)
);

-- Situs 変更ログ（所有権移転の記録）
CREATE TABLE thing_situs_log (
  id TEXT PRIMARY KEY,
  thing_id TEXT NOT NULL,
  from_situs TEXT NOT NULL,
  to_situs TEXT NOT NULL,
  reason_type TEXT NOT NULL,
  reason_detail TEXT,
  contract_ref TEXT,
  created_at REAL NOT NULL,
  FOREIGN KEY (thing_id) REFERENCES thing(id)
);

-- Protention（予持：未来の Pending Intent）
CREATE TABLE thing_protention (
  id TEXT PRIMARY KEY,
  thing_id TEXT NOT NULL,
  scheduled_at REAL NOT NULL,
  intent_body TEXT NOT NULL,
  condition TEXT,
  status TEXT NOT NULL DEFAULT 'pending',
  created_at REAL NOT NULL,
  FOREIGN KEY (thing_id) REFERENCES thing(id)
);
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
