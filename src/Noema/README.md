# Noema

## 役割

Noema DSL の中核モジュール。圏論的随伴構造（Intent ⊣ Cognition）に基づき、意志の構造化と実行を分離する。

## 圏論的位置づけ

Noema は以下の随伴関係を実現する：

```
Intent ⊣ Cognition : Struct ⇄ Prop
```

- **Struct 圏**: 意志の構造化された空間（Vorzeichnung）
- **Prop 圏**: 認知可能な事実の空間（Effect）
- **随伴**: Intent（左随伴・自由）と Cognition（右随伴・忘却）

この随伴により、意図の静的構造と動的実行が自然に対応する。

## サブモジュール

| モジュール | 圏論的役割 | 説明 |
|-----------|-----------|------|
| [Vorzeichnung/](Vorzeichnung/README.md) | 左随伴（自由関手） | 意図の構造化 |
| [Cognition/](Cognition/README.md) | 右随伴（忘却関手） | 意図の解釈・実行 |
| Sedimentation/ | 代数の台 | 状態の沈殿・定着 |
| Presheaf/ | 関手圏 | 外界への表現（Channel^op → Set） |

## 層構造

```
Vorzeichnung（意図）
     │
     │ Intent: 静的構造（Arrow Effects）
     │
     ▼
Cognition（認知）
     │
     │ Handler: 自然変換 f ~> m
     │
     ▼
Sedimentation（沈殿）
     │
     │ Attractor: 状態の定着
     │
     ▼
Presheaf（表現）
     │
     │ Channel^op → Set
     │
     ▼
外界（販売チャネル）
```

## 設計原則

1. **Arrow Effects（分岐禁止）**: ArrowChoice を実装しない。分岐は Cognition の責務
2. **技術非依存**: Platform/ に依存しない
3. **TLA+ 対応**: Intent の構造は TLA+ でモデル検証可能

## 関連

- [../Control/](../Control/README.md) - Arrow 型クラス実装
- [../Platform/](../Platform/) - プラットフォーム固有実装
- [../TlaPlus/](../TlaPlus/) - TLA+ 連携
