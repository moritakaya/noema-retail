# Noema-Retail リファクタリング手順書

## 目的

DDDベースの構造から、圏論的随伴構造を反映したモジュール分割へ移行する。

## 圏論的原則

```
Intent ⊣ Cognition （随伴）
  │         │
  ▼         ▼
Free F    Forgetful U
  │         │
  ▼         ▼
Vorzeichnung → Cognition → Sedimentation → Presheaf
```

---

## Phase 1: ディレクトリ構造の準備

```bash
# 新しいディレクトリ構造を作成
mkdir -p src/Noema/Vorzeichnung/Vocabulary
mkdir -p src/Noema/Cognition
mkdir -p src/Noema/Sedimentation
mkdir -p src/Noema/Presheaf
mkdir -p src/Platform/Cloudflare/FFI
```

---

## Phase 2: Vorzeichnung（予描図式）の構成

### 2.1 Freer Monad の移動

```bash
# Intent/ → Vorzeichnung/
mv src/Noema/Intent/Freer.purs src/Noema/Vorzeichnung/Freer.purs
rmdir src/Noema/Intent
```

**Freer.purs のモジュール名を更新:**

```purescript
-- 旧: module Noema.Intent.Freer
-- 新:
module Noema.Vorzeichnung.Freer where
```

### 2.2 Vocabulary（語彙）の統合

Effect/ と Domain/ の Functor を Vocabulary/ に集約:

```bash
# Effect/ → Vocabulary/
mv src/Noema/Effect/HttpF.purs src/Noema/Vorzeichnung/Vocabulary/HttpF.purs
mv src/Noema/Effect/HttpF.js src/Noema/Vorzeichnung/Vocabulary/HttpF.js
mv src/Noema/Effect/StorageF.purs src/Noema/Vorzeichnung/Vocabulary/StorageF.purs
rmdir src/Noema/Effect

# Domain/ → Vocabulary/
mv src/Noema/Domain/Base.purs src/Noema/Vorzeichnung/Vocabulary/Base.purs
mv src/Noema/Domain/Base.js src/Noema/Vorzeichnung/Vocabulary/Base.js
mv src/Noema/Domain/Inventory.purs src/Noema/Vorzeichnung/Vocabulary/InventoryF.purs
rmdir src/Noema/Domain
```

**モジュール名の更新パターン:**

```purescript
-- 旧: module Noema.Effect.HttpF
-- 新: module Noema.Vorzeichnung.Vocabulary.HttpF

-- 旧: module Noema.Domain.Inventory
-- 新: module Noema.Vorzeichnung.Vocabulary.InventoryF
```

### 2.3 RetailF（余積）の作成

`src/Noema/Vorzeichnung/Vocabulary/RetailF.purs` を新規作成:

```purescript
module Noema.Vorzeichnung.Vocabulary.RetailF where

import Prelude
import Data.Functor.Coproduct (Coproduct)

import Noema.Vorzeichnung.Vocabulary.InventoryF (InventoryF)
import Noema.Vorzeichnung.Vocabulary.HttpF (HttpF)
import Noema.Vorzeichnung.Vocabulary.StorageF (StorageF)

-- | 語彙の余積 = Noema の「意志のアルファベット」
type RetailF = Coproduct InventoryF (Coproduct HttpF StorageF)
```

---

## Phase 3: Cognition（認知）の構成

### 3.1 Handler の移動

```bash
mv src/Noema/Handler/InventoryHandler.purs src/Noema/Cognition/InventoryHandler.purs
mv src/Noema/Handler/InventoryHandler.js src/Noema/Cognition/InventoryHandler.js
mv src/Noema/Handler/StorageHandler.purs src/Noema/Cognition/StorageHandler.purs
rmdir src/Noema/Handler
```

**モジュール名の更新:**

```purescript
-- 旧: module Noema.Handler.InventoryHandler
-- 新: module Noema.Cognition.InventoryHandler
```

### 3.2 Collapse（崩落）の新規作成

`src/Noema/Cognition/Collapse.purs`:

```purescript
module Noema.Cognition.Collapse where

import Prelude
import Control.Monad.Free (foldFree)
import Data.Functor.Coproduct (Coproduct, coproduct)

import Noema.Vorzeichnung.Freer (Intent)
import Noema.Vorzeichnung.Vocabulary.RetailF (RetailF)

-- | 意志の構造を事実へ崩落させる
-- | 圏論的には: 忘却関手 U による解釈
collapse 
  :: forall m
   . Monad m 
  => (forall a. RetailF a -> m a) 
  -> Intent ~> m
collapse handler = foldFree handler
```

---

## Phase 4: Sedimentation（沈殿）の構成

### 4.1 抽象 Attractor の作成

`src/Noema/Sedimentation/Attractor.purs`:

```purescript
module Noema.Sedimentation.Attractor where

import Prelude
import Noema.Vorzeichnung.Freer (Intent)

-- | 沈殿の封印（トランザクション結果）
newtype Seal = Seal
  { success :: Boolean
  , version :: Int
  , hash :: String
  }

-- | Attractor: 意志が沈殿する引き込み域
-- | 具体的な実装は Platform/ で提供
class Attractor a where
  sediment :: Intent ~> a Seal
```

### 4.2 Seal と Cryostasis

`src/Noema/Sedimentation/Seal.purs`:

```purescript
module Noema.Sedimentation.Seal where

-- | 封印: トランザクションの完了証明
newtype Seal = Seal
  { success :: Boolean
  , version :: Int
  , hash :: String
  , timestamp :: Number
  }

derive instance eqSeal :: Eq Seal
```

`src/Noema/Sedimentation/Cryostasis.purs`:

```purescript
module Noema.Sedimentation.Cryostasis where

import Noema.Sedimentation.Seal (Seal)

-- | 凍結状態: Alarm による復活待ち
type Cryostasis =
  { state :: Foreign
  , nomosHash :: String
  , sieve :: Array String  -- 依存スキーマ
  , frozenAt :: Number
  , wakeAt :: Number
  }
```

---

## Phase 5: Presheaf（表現関手）の構成

### 5.1 Channel 圏の定義

`src/Noema/Presheaf/Channel.purs`:

```purescript
module Noema.Presheaf.Channel where

import Prelude

-- | Channel 圏の対象
data Channel
  = Own        -- 自社（Noema が真実）
  | Smaregi    -- スマレジ POS
  | Rakuten    -- 楽天市場
  | Yahoo      -- Yahoo!ショッピング
  | Stripe     -- Stripe 決済

derive instance eqChannel :: Eq Channel
derive instance ordChannel :: Ord Channel

-- | Channel 間の射（同期方向）
-- | 圏論的には Channel^op → Set の自然変換
data ChannelMorphism
  = SyncTo Channel Channel
  | Broadcast Channel (Array Channel)
```

### 5.2 Adapter の移動

```bash
# Adapter/ → Presheaf/
mv src/Adapter/ChannelAdapter.purs src/Noema/Presheaf/ChannelAdapter.purs
mv src/Adapter/ChannelAdapter.js src/Noema/Presheaf/ChannelAdapter.js
mv src/Adapter/SmaregiAdapter.purs src/Noema/Presheaf/Smaregi.purs
mv src/Adapter/SmaregiAdapter.js src/Noema/Presheaf/Smaregi.js
mv src/Adapter/RakutenAdapter.purs src/Noema/Presheaf/Rakuten.purs
mv src/Adapter/YahooAdapter.purs src/Noema/Presheaf/Yahoo.purs
mv src/Adapter/YahooAdapter.js src/Noema/Presheaf/Yahoo.js
mv src/Adapter/StripeAdapter.purs src/Noema/Presheaf/Stripe.purs
mv src/Adapter/StripeAdapter.js src/Noema/Presheaf/Stripe.js
rmdir src/Adapter
```

**モジュール名の更新:**

```purescript
-- 旧: module Adapter.SmaregiAdapter
-- 新: module Noema.Presheaf.Smaregi
```

---

## Phase 6: Platform（プラットフォーム実装）の構成

### 6.1 Cloudflare 固有実装の分離

```bash
# Workers/ → Platform/Cloudflare/
mv src/Workers/Attractor/InventoryAttractor.purs src/Platform/Cloudflare/InventoryAttractor.purs
mv src/Workers/Attractor/InventoryAttractor.js src/Platform/Cloudflare/InventoryAttractor.js
mv src/Workers/Router.purs src/Platform/Cloudflare/Router.purs
mv src/Workers/Router.js src/Platform/Cloudflare/Router.js

# FFI の移動
mv src/Workers/FFI/* src/Platform/Cloudflare/FFI/
rmdir src/Workers/FFI
rmdir src/Workers/Attractor
rmdir src/Workers
```

**モジュール名の更新:**

```purescript
-- 旧: module Workers.Attractor.InventoryAttractor
-- 新: module Platform.Cloudflare.InventoryAttractor

-- 旧: module Workers.FFI.DurableObject
-- 新: module Platform.Cloudflare.FFI.DurableObject
```

---

## Phase 7: Import の一括更新

すべてのファイルで import パスを更新する必要がある。

### 更新マッピング

| 旧 | 新 |
|----|-----|
| `Noema.Intent.Freer` | `Noema.Vorzeichnung.Freer` |
| `Noema.Effect.HttpF` | `Noema.Vorzeichnung.Vocabulary.HttpF` |
| `Noema.Effect.StorageF` | `Noema.Vorzeichnung.Vocabulary.StorageF` |
| `Noema.Domain.Base` | `Noema.Vorzeichnung.Vocabulary.Base` |
| `Noema.Domain.Inventory` | `Noema.Vorzeichnung.Vocabulary.InventoryF` |
| `Noema.Handler.*` | `Noema.Cognition.*` |
| `Adapter.*` | `Noema.Presheaf.*` |
| `Workers.Attractor.*` | `Platform.Cloudflare.*` |
| `Workers.FFI.*` | `Platform.Cloudflare.FFI.*` |

### sed による一括置換

```bash
# macOS の場合は gsed を使用（brew install gnu-sed）
find src -name "*.purs" -exec sed -i \
  -e 's/Noema\.Intent\.Freer/Noema.Vorzeichnung.Freer/g' \
  -e 's/Noema\.Effect\./Noema.Vorzeichnung.Vocabulary./g' \
  -e 's/Noema\.Domain\.Base/Noema.Vorzeichnung.Vocabulary.Base/g' \
  -e 's/Noema\.Domain\.Inventory/Noema.Vorzeichnung.Vocabulary.InventoryF/g' \
  -e 's/Noema\.Handler\./Noema.Cognition./g' \
  -e 's/Adapter\./Noema.Presheaf./g' \
  -e 's/Workers\.Attractor\./Platform.Cloudflare./g' \
  -e 's/Workers\.FFI\./Platform.Cloudflare.FFI./g' \
  {} \;
```

---

## Phase 8: ビルドと検証

```bash
# PureScript ビルド
spago build

# エラーがあれば修正

# Workers ビルド
npm run build

# ローカルテスト
wrangler dev
```

---

## 最終ディレクトリ構造

```
noema-retail/
├── src/
│   ├── Main.purs
│   │
│   ├── Noema/
│   │   ├── Vorzeichnung/           # 予描図式（左随伴 Free F）
│   │   │   ├── Freer.purs
│   │   │   └── Vocabulary/
│   │   │       ├── Base.purs
│   │   │       ├── InventoryF.purs
│   │   │       ├── HttpF.purs
│   │   │       ├── StorageF.purs
│   │   │       └── RetailF.purs
│   │   │
│   │   ├── Cognition/              # 認知（右随伴 Forgetful U）
│   │   │   ├── Collapse.purs
│   │   │   ├── InventoryHandler.purs
│   │   │   └── StorageHandler.purs
│   │   │
│   │   ├── Sedimentation/          # 沈殿（状態の定着）
│   │   │   ├── Attractor.purs
│   │   │   ├── Seal.purs
│   │   │   └── Cryostasis.purs
│   │   │
│   │   └── Presheaf/               # 表現（Channel^op → Set）
│   │       ├── Channel.purs
│   │       ├── ChannelAdapter.purs
│   │       ├── Smaregi.purs
│   │       ├── Rakuten.purs
│   │       ├── Yahoo.purs
│   │       └── Stripe.purs
│   │
│   └── Platform/
│       └── Cloudflare/
│           ├── InventoryAttractor.purs
│           ├── Router.purs
│           └── FFI/
│               ├── DurableObject.purs
│               ├── SqlStorage.purs
│               ├── Fetch.purs
│               ├── Crypto.purs
│               ├── Request.purs
│               └── Response.purs
│
├── ffi/
│   └── runtime.js
│
├── .claude/rules/
└── docs/
```

---

## 検証チェックリスト

- [ ] `spago build` が成功する
- [ ] `npm run build` が成功する
- [ ] `wrangler dev` でローカル起動できる
- [ ] 既存のAPIエンドポイントが動作する
- [ ] Durable Object が正常に動作する

---

## 備考

このリファクタリングは**構造的変更のみ**で、ロジックの変更は含まない。
ディレクトリ名とモジュール名の変更により、コードベースが圏論的随伴構造を反映するようになる。
