# Noema Documentation Policy (CLAUDE.md に追記)

## ドキュメント方針

Noema は既存の設計手法（DDD, Clean Architecture 等）に依存しない、
圏論的基盤に基づく DSL である。自然言語による設計書を重視する。

### 必須ルール

1. **新規ディレクトリには必ず README.md を配置**
   - ディレクトリ作成と同時に README.md もコミット
   - 空のディレクトリは許可しない

2. **README.md の必須セクション**
   ```markdown
   # [ディレクトリ名]
   
   ## 役割
   このモジュールの責務を1-2文で説明。
   
   ## 圏論的位置づけ
   - どの圏に属するか（Intent圏、Cognition圏、etc）
   - 他モジュールとの関手的関係
   - 随伴関係があれば明記
   
   ## 主要コンポーネント
   - `File.purs`: 説明
   
   ## 使用例
   ```purescript
   example = ...
   ```
   ```

3. **圏論的記述を優先**
   - ✅ 使う: Intent, Cognition, Vorzeichnung, 随伴, 関手, 自然変換
   - ❌ 避ける: Entity, Repository, Service, Aggregate, UseCase

4. **コミットメッセージ**
   - ディレクトリ追加時: `docs:` プレフィックスで README も言及
   - 例: `feat(inventory): Add reservation module with docs`

### ドキュメント階層

```
/
├── README.md              # プロジェクト全体概要
├── CLAUDE.md              # AI向けガイドライン（このファイル）
├── docs/
│   ├── design-principles.md   # 設計原理詳細
│   ├── category-theory.md     # 圏論的基盤
│   └── tla-pipeline.md        # TLA+検証
├── src/
│   └── [Module]/
│       └── README.md      # 各モジュールの説明
└── tlaplus/
    └── README.md          # TLA+仕様の説明
```

### Noema 固有の用語

| Noema用語 | 意味 | DDD等価物（参考のみ） |
|-----------|------|----------------------|
| Intent | 意図の静的構造 | Command/Query |
| Cognition | 意図の解釈・実行 | Handler |
| Vorzeichnung | 前描画スキーマ | - |
| Vocabulary | ドメイン語彙 | Domain Model |
| Arrow Effects | 分岐禁止の効果系 | Effect System |

### 設計書更新のトリガー

以下の変更時は必ず関連ドキュメントを更新：
- 新規モジュール追加
- 公開 API の変更
- 圏論的構造の変更
- TLA+ 仕様の追加・変更

---

## 補足: なぜ自然言語の設計書を重視するか

1. **LLM との協働**: AI がコードベースを理解しやすくなる
2. **圏論的構造の明示**: 型だけでは伝わらない設計意図を補完
3. **知識の永続化**: 開発者の交代に備える
4. **TLA+ との対応**: 形式仕様と実装の対応を記述
