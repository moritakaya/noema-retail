# Claude Code タスク: Noema 設計書の充実化

## 概要

Noema は圏論的基盤に基づく新しい DSL である。DDD などの既存設計手法に捉われず、独自の構造を持つ。自然言語の設計書を充実させ、開発者（人間・AI 両方）が理解しやすい形にする。

---

## タスク1: README.md の更新

### 現状
README.md が古いまま。Arrow 移行、TLA+ パイプライン追加などが反映されていない。

### 更新すべき内容

```markdown
# Noema Retail

## 概要
Noema は圏論的基盤に基づく分散システム DSL。
Intent（意図）と Cognition（認知）の随伴関係により、
副作用の構造と実行を分離する。

## 設計原理

### Intent ⊣ Cognition 随伴
- Intent: 「何をしたいか」の静的構造（Arrow Effects）
- Cognition: 「どう実行するか」の動的解釈（Handler）
- 両者は圏論的随伴関係を形成

### Arrow Effects（分岐禁止）
- ArrowChoice を意図的に実装しない
- 分岐は Cognition（Handler）の責務
- TLA+ でのモデル検証が容易

### Vorzeichnung（前描画スキーマ）
- Husserl の現象学から着想
- 実行前に Intent の全構造が確定
- 「実行は忘却である」

## ディレクトリ構造
src/
├── Noema/
│   ├── Vorzeichnung/        # 意図の構造
│   │   ├── Intent.purs      # Arrow-based Intent
│   │   └── Vocabulary/      # ドメイン語彙
│   └── Cognition/           # 実行・解釈
│       └── Handler/         # Effect handlers
├── Control/
│   └── Arrow.purs           # Arrow 実装
└── ...

tlaplus/
└── specs/                   # TLA+ 形式検証
    ├── InventorySimple.tla
    └── InventorySimple.cfg

## 圏論的対応

| 概念 | PureScript | TLA+ |
|------|------------|------|
| 逐次合成 | `f >>> g` | F ∘ G |
| 並列合成 | `f *** g` | F ∧ G |
| 純粋変換 | `arr f` | vars' = f(vars) |
| 効果 | `liftEffect` | Action |

## 開発ガイド
- [設計原理](docs/design-principles.md)
- [Intent 記述ガイド](src/Noema/Vorzeichnung/README.md)
- [Handler 実装ガイド](src/Noema/Cognition/README.md)
- [TLA+ 検証](tlaplus/README.md)
```

---

## タスク2: 各ディレクトリに README.md を配置

### 必要なファイル

1. **`src/Noema/README.md`** - Noema 全体の説明
2. **`src/Noema/Vorzeichnung/README.md`** - Intent 層の説明
3. **`src/Noema/Vorzeichnung/Vocabulary/README.md`** - 語彙の説明
4. **`src/Noema/Cognition/README.md`** - Cognition 層の説明（存在すれば）
5. **`src/Control/README.md`** - Arrow 実装の説明
6. **`tlaplus/README.md`** - TLA+ パイプラインの説明
7. **`docs/design-principles.md`** - 設計原理の詳細

### 各 README のテンプレート

```markdown
# [ディレクトリ名]

## 役割
このモジュールの責務を1-2文で。

## 圏論的位置づけ
- どの圏に属するか
- 他モジュールとの関手的関係

## 主要コンポーネント
- `File1.purs`: 説明
- `File2.purs`: 説明

## 使用例
```purescript
-- コード例
```

## 関連
- [親ディレクトリ](../README.md)
- [関連モジュール](../Other/README.md)
```

---

## タスク3: Skill 化の検討と実装

### 目的
今後の開発でも設計書記述を徹底するため、Claude Code に方針を伝えるスキルを作成。

### 推奨: CLAUDE.md に追記

`CLAUDE.md`（プロジェクトルート）に以下を追加：

```markdown
## 設計書ポリシー

### 必須ルール
1. 新しいディレクトリを作成したら、必ず README.md を配置
2. README.md には以下を含める：
   - 役割（1-2文）
   - 圏論的位置づけ
   - 主要コンポーネント
   - 使用例

### 設計書の階層
- `/README.md` - プロジェクト全体
- `/src/*/README.md` - 各モジュール
- `/docs/*.md` - 詳細ドキュメント

### 圏論的記述
- モジュール間の関係は圏論的に記述
- 随伴、関手、自然変換などの用語を使用
- DDD 用語（Entity, Repository 等）は使わない

### コミット時
新規ディレクトリ追加時は README.md も同時にコミット
```

### 代替案: スキルファイル作成

`.claude/skills/documentation.md` を作成：

```markdown
# Noema Documentation Skill

## When to Apply
- 新規ディレクトリ作成時
- モジュール追加時
- 大きなリファクタリング後

## Rules
1. 各ディレクトリに README.md を配置
2. 圏論的な位置づけを記述
3. DDD 用語を避け、Noema 独自の用語を使用
4. Intent/Cognition/Vorzeichnung の関係を明示

## Template
[READMEテンプレート]
```

---

## 実行手順

1. まずプロジェクト構造を確認
   ```bash
   find src -type d
   ls -la
   cat README.md
   ```

2. README.md を更新

3. 各ディレクトリに README.md を作成

4. CLAUDE.md に設計書ポリシーを追加

5. コミット
   ```bash
   git add .
   git commit -m "docs: Add comprehensive documentation for Noema DSL
   
   - Update root README.md with current architecture
   - Add README.md to each module directory
   - Document category-theoretic foundations
   - Add documentation policy to CLAUDE.md
   
   Noema uses Intent ⊣ Cognition adjunction instead of traditional DDD.
   Arrow Effects (no ArrowChoice) enable TLA+ model checking."
   
   git push
   ```

---

## 期待される成果物

```
noema-retail/
├── README.md                          # 更新済み
├── CLAUDE.md                          # 設計書ポリシー追加
├── docs/
│   ├── design-principles.md           # 新規
│   └── tla-pipeline.md                # 既存
├── src/
│   ├── Noema/
│   │   ├── README.md                  # 新規
│   │   ├── Vorzeichnung/
│   │   │   ├── README.md              # 新規
│   │   │   └── Vocabulary/
│   │   │       └── README.md          # 新規
│   │   └── Cognition/
│   │       └── README.md              # 新規（存在すれば）
│   └── Control/
│       └── README.md                  # 新規
└── tlaplus/
    └── README.md                      # 新規
```
