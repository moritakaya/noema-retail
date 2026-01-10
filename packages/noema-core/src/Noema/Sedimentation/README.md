# Sedimentation

## 役割

Sedimentation（沈殿）は Cognition による解釈の結果を管理する。
Factum（流動的事実）から Seal（確定した事実）への沈殿過程を表現する。

## 圏論的位置づけ

```
Presheaf（前層）
    ↓ 層化関手 a
Sheaf（層）= Sedimentation の結果
```

| 概念 | 圏論 | 実装 |
|------|------|------|
| **Factum** | 流動的事実 | `Factum.purs` |
| **Seal** | 確定した事実 | `Seal.purs` |
| **Precedent** | 判例（棄却されたケース） | `Precedent.purs` |
| **Attractor** | A-algebra | DO（InventoryAttractor 等） |

## 主要コンポーネント

- `Factum.purs`: 流動的事実（newtype Factum a = Factum (Effect a)）
- `Seal.purs`: 確定した事実の証明
- `Precedent.purs`: 判例記録（棄却されたケースの履歴）

## Factum と Effect の関係

```purescript
newtype Factum a = Factum (Effect a)

-- Effect → Factum（認識）
recognize :: Effect a -> Factum a

-- Factum → Effect（忘却・崩落）
collapse :: Factum a -> Effect a
```

### なぜ Factum を Effect と分離するか

1. **意味論的区別**: Effect は「副作用」、Factum は「認識された事実」
2. **境界の明確化**: 外界との接点（collapse）を明示的に制御
3. **テスト容易性**: Factum レベルでのモック化が可能

## Precedent（判例）

Noema には「エラー」という概念はない。
Cognition が正常に崩落しなかったケースは「判例」として記録される。

```purescript
data SuspensionOutcome
  = Sedimented SedimentId World  -- 正常に沈殿
  | Abandoned                     -- ユーザーによる取り消し
  | Rejected World Reason         -- 判例

-- 判例は将来の Nomos 改訂に影響
verifyConnectionWithPrecedent
  :: PrecedentLog
  -> World
  -> World
  -> ConnectionType
```

## 沈殿の流れ

```
Intent（意志）
    │
    ↓ Interpretation（解釈）
Factum（流動的事実）
    │
    ↓ Attractor.sediment（沈殿過程）
Seal（確定した事実）+ World
    │
    ↓ collapse（忘却）
Effect（外界への崩落）
```

## 使用例

```purescript
import Noema.Sedimentation.Factum (Factum, recognize, collapse)
import Noema.Sedimentation.Seal (Seal, SealId)
import Noema.Sedimentation.Precedent (PrecedentLog, addPrecedent)

-- Factum の作成
myFactum :: Factum Int
myFactum = recognize $ pure 42

-- Factum の合成（Monad）
combined :: Factum String
combined = do
  x <- recognize $ pure 10
  y <- recognize $ pure 20
  pure $ show (x + y)

-- Effect への崩落（エントリーポイントで）
main :: Effect Unit
main = collapse do
  result <- combined
  recognize $ log result
```

## 他のモジュールとの関係

```
Cognition/Interpretation.purs
        │
        ↓ f ~> Factum
Sedimentation/
├── Factum.purs ─────────────────► collapse ► Effect
├── Seal.purs    ─────────────────► DO に永続化
└── Precedent.purs ───────────────► 判例記録（Nomos 改訂に影響）
        │
        ↓
Platform/Cloudflare/
├── InventoryAttractor.purs
└── SubjectAttractor.purs
```
