#!/bin/bash
# Noema-Retail リファクタリングスクリプト
# Claude Code セッションで実行

set -e  # エラー時に停止

echo "=== Noema-Retail リファクタリング開始 ==="

# 作業ディレクトリの確認
if [ ! -f "spago.yaml" ]; then
  echo "エラー: noema-retail ディレクトリで実行してください"
  exit 1
fi

# バックアップ
echo "Phase 0: バックアップ作成..."
git stash -u || true
git checkout -b refactor/categorical-structure 2>/dev/null || git checkout refactor/categorical-structure

# ========================================
# Phase 1: ディレクトリ構造の準備
# ========================================
echo "Phase 1: ディレクトリ構造の準備..."

mkdir -p src/Noema/Vorzeichnung/Vocabulary
mkdir -p src/Noema/Cognition
mkdir -p src/Noema/Sedimentation
mkdir -p src/Noema/Presheaf
mkdir -p src/Platform/Cloudflare/FFI

# ========================================
# Phase 2: Vorzeichnung（予描図式）
# ========================================
echo "Phase 2: Vorzeichnung の構成..."

# 2.1 Freer Monad
if [ -f "src/Noema/Intent/Freer.purs" ]; then
  mv src/Noema/Intent/Freer.purs src/Noema/Vorzeichnung/Freer.purs
  rmdir src/Noema/Intent 2>/dev/null || true
fi

# 2.2 Effect/ → Vocabulary/
if [ -d "src/Noema/Effect" ]; then
  mv src/Noema/Effect/HttpF.purs src/Noema/Vorzeichnung/Vocabulary/HttpF.purs 2>/dev/null || true
  mv src/Noema/Effect/HttpF.js src/Noema/Vorzeichnung/Vocabulary/HttpF.js 2>/dev/null || true
  mv src/Noema/Effect/StorageF.purs src/Noema/Vorzeichnung/Vocabulary/StorageF.purs 2>/dev/null || true
  rmdir src/Noema/Effect 2>/dev/null || true
fi

# 2.3 Domain/ → Vocabulary/
if [ -d "src/Noema/Domain" ]; then
  mv src/Noema/Domain/Base.purs src/Noema/Vorzeichnung/Vocabulary/Base.purs 2>/dev/null || true
  mv src/Noema/Domain/Base.js src/Noema/Vorzeichnung/Vocabulary/Base.js 2>/dev/null || true
  mv src/Noema/Domain/Inventory.purs src/Noema/Vorzeichnung/Vocabulary/InventoryF.purs 2>/dev/null || true
  rmdir src/Noema/Domain 2>/dev/null || true
fi

# ========================================
# Phase 3: Cognition（認知）
# ========================================
echo "Phase 3: Cognition の構成..."

if [ -d "src/Noema/Handler" ]; then
  mv src/Noema/Handler/InventoryHandler.purs src/Noema/Cognition/InventoryHandler.purs 2>/dev/null || true
  mv src/Noema/Handler/InventoryHandler.js src/Noema/Cognition/InventoryHandler.js 2>/dev/null || true
  mv src/Noema/Handler/StorageHandler.purs src/Noema/Cognition/StorageHandler.purs 2>/dev/null || true
  rmdir src/Noema/Handler 2>/dev/null || true
fi

# ========================================
# Phase 4: Presheaf（表現関手）
# ========================================
echo "Phase 4: Presheaf の構成..."

if [ -d "src/Adapter" ]; then
  mv src/Adapter/ChannelAdapter.purs src/Noema/Presheaf/ChannelAdapter.purs 2>/dev/null || true
  mv src/Adapter/ChannelAdapter.js src/Noema/Presheaf/ChannelAdapter.js 2>/dev/null || true
  mv src/Adapter/SmaregiAdapter.purs src/Noema/Presheaf/Smaregi.purs 2>/dev/null || true
  mv src/Adapter/SmaregiAdapter.js src/Noema/Presheaf/Smaregi.js 2>/dev/null || true
  mv src/Adapter/RakutenAdapter.purs src/Noema/Presheaf/Rakuten.purs 2>/dev/null || true
  mv src/Adapter/YahooAdapter.purs src/Noema/Presheaf/Yahoo.purs 2>/dev/null || true
  mv src/Adapter/YahooAdapter.js src/Noema/Presheaf/Yahoo.js 2>/dev/null || true
  mv src/Adapter/StripeAdapter.purs src/Noema/Presheaf/Stripe.purs 2>/dev/null || true
  mv src/Adapter/StripeAdapter.js src/Noema/Presheaf/Stripe.js 2>/dev/null || true
  rmdir src/Adapter 2>/dev/null || true
fi

# ========================================
# Phase 5: Platform（プラットフォーム実装）
# ========================================
echo "Phase 5: Platform の構成..."

if [ -d "src/Workers" ]; then
  # Attractor
  mv src/Workers/Attractor/InventoryAttractor.purs src/Platform/Cloudflare/InventoryAttractor.purs 2>/dev/null || true
  mv src/Workers/Attractor/InventoryAttractor.js src/Platform/Cloudflare/InventoryAttractor.js 2>/dev/null || true
  rmdir src/Workers/Attractor 2>/dev/null || true
  
  # Router
  mv src/Workers/Router.purs src/Platform/Cloudflare/Router.purs 2>/dev/null || true
  mv src/Workers/Router.js src/Platform/Cloudflare/Router.js 2>/dev/null || true
  
  # FFI
  if [ -d "src/Workers/FFI" ]; then
    mv src/Workers/FFI/* src/Platform/Cloudflare/FFI/ 2>/dev/null || true
    rmdir src/Workers/FFI 2>/dev/null || true
  fi
  
  rmdir src/Workers 2>/dev/null || true
fi

# ========================================
# Phase 6: モジュール名の更新
# ========================================
echo "Phase 6: モジュール名の更新..."

# PureScript ファイルのモジュール名を更新
find src -name "*.purs" -type f | while read file; do
  # macOS と Linux 両対応
  if [[ "$OSTYPE" == "darwin"* ]]; then
    sed -i '' \
      -e 's/module Noema\.Intent\.Freer/module Noema.Vorzeichnung.Freer/g' \
      -e 's/module Noema\.Effect\.HttpF/module Noema.Vorzeichnung.Vocabulary.HttpF/g' \
      -e 's/module Noema\.Effect\.StorageF/module Noema.Vorzeichnung.Vocabulary.StorageF/g' \
      -e 's/module Noema\.Domain\.Base/module Noema.Vorzeichnung.Vocabulary.Base/g' \
      -e 's/module Noema\.Domain\.Inventory/module Noema.Vorzeichnung.Vocabulary.InventoryF/g' \
      -e 's/module Noema\.Handler\./module Noema.Cognition./g' \
      -e 's/module Adapter\./module Noema.Presheaf./g' \
      -e 's/module Workers\.Attractor\./module Platform.Cloudflare./g' \
      -e 's/module Workers\.FFI\./module Platform.Cloudflare.FFI./g' \
      -e 's/module Workers\.Router/module Platform.Cloudflare.Router/g' \
      "$file"
  else
    sed -i \
      -e 's/module Noema\.Intent\.Freer/module Noema.Vorzeichnung.Freer/g' \
      -e 's/module Noema\.Effect\.HttpF/module Noema.Vorzeichnung.Vocabulary.HttpF/g' \
      -e 's/module Noema\.Effect\.StorageF/module Noema.Vorzeichnung.Vocabulary.StorageF/g' \
      -e 's/module Noema\.Domain\.Base/module Noema.Vorzeichnung.Vocabulary.Base/g' \
      -e 's/module Noema\.Domain\.Inventory/module Noema.Vorzeichnung.Vocabulary.InventoryF/g' \
      -e 's/module Noema\.Handler\./module Noema.Cognition./g' \
      -e 's/module Adapter\./module Noema.Presheaf./g' \
      -e 's/module Workers\.Attractor\./module Platform.Cloudflare./g' \
      -e 's/module Workers\.FFI\./module Platform.Cloudflare.FFI./g' \
      -e 's/module Workers\.Router/module Platform.Cloudflare.Router/g' \
      "$file"
  fi
done

# ========================================
# Phase 7: Import の更新
# ========================================
echo "Phase 7: Import の更新..."

find src -name "*.purs" -type f | while read file; do
  if [[ "$OSTYPE" == "darwin"* ]]; then
    sed -i '' \
      -e 's/import Noema\.Intent\.Freer/import Noema.Vorzeichnung.Freer/g' \
      -e 's/import Noema\.Effect\./import Noema.Vorzeichnung.Vocabulary./g' \
      -e 's/import Noema\.Domain\.Base/import Noema.Vorzeichnung.Vocabulary.Base/g' \
      -e 's/import Noema\.Domain\.Inventory/import Noema.Vorzeichnung.Vocabulary.InventoryF/g' \
      -e 's/import Noema\.Handler\./import Noema.Cognition./g' \
      -e 's/import Adapter\./import Noema.Presheaf./g' \
      -e 's/import Workers\.Attractor\./import Platform.Cloudflare./g' \
      -e 's/import Workers\.FFI\./import Platform.Cloudflare.FFI./g' \
      -e 's/import Workers\.Router/import Platform.Cloudflare.Router/g' \
      "$file"
  else
    sed -i \
      -e 's/import Noema\.Intent\.Freer/import Noema.Vorzeichnung.Freer/g' \
      -e 's/import Noema\.Effect\./import Noema.Vorzeichnung.Vocabulary./g' \
      -e 's/import Noema\.Domain\.Base/import Noema.Vorzeichnung.Vocabulary.Base/g' \
      -e 's/import Noema\.Domain\.Inventory/import Noema.Vorzeichnung.Vocabulary.InventoryF/g' \
      -e 's/import Noema\.Handler\./import Noema.Cognition./g' \
      -e 's/import Adapter\./import Noema.Presheaf./g' \
      -e 's/import Workers\.Attractor\./import Platform.Cloudflare./g' \
      -e 's/import Workers\.FFI\./import Platform.Cloudflare.FFI./g' \
      -e 's/import Workers\.Router/import Platform.Cloudflare.Router/g' \
      "$file"
  fi
done

# ========================================
# Phase 8: 新規ファイルの作成
# ========================================
echo "Phase 8: 新規ファイルの作成..."

# RetailF.purs（語彙の余積）
cat > src/Noema/Vorzeichnung/Vocabulary/RetailF.purs << 'EOF'
module Noema.Vorzeichnung.Vocabulary.RetailF where

import Prelude
import Data.Functor.Coproduct (Coproduct)

import Noema.Vorzeichnung.Vocabulary.InventoryF (InventoryF)
import Noema.Vorzeichnung.Vocabulary.HttpF (HttpF)
import Noema.Vorzeichnung.Vocabulary.StorageF (StorageF)

-- | 語彙の余積 = Noema の「意志のアルファベット」
-- | 圏論的には: RetailF = InventoryF + HttpF + StorageF
type RetailF = Coproduct InventoryF (Coproduct HttpF StorageF)
EOF

# Channel.purs
cat > src/Noema/Presheaf/Channel.purs << 'EOF'
module Noema.Presheaf.Channel where

import Prelude

-- | Channel 圏の対象
-- | Inventory は Presheaf: Channel^op → Set
data Channel
  = Own        -- 自社（Noema が Single Source of Truth）
  | Smaregi    -- スマレジ POS
  | Rakuten    -- 楽天市場
  | Yahoo      -- Yahoo!ショッピング
  | Stripe     -- Stripe 決済

derive instance eqChannel :: Eq Channel
derive instance ordChannel :: Ord Channel

instance showChannel :: Show Channel where
  show Own = "Own"
  show Smaregi = "Smaregi"
  show Rakuten = "Rakuten"
  show Yahoo = "Yahoo"
  show Stripe = "Stripe"
EOF

# Seal.purs
cat > src/Noema/Sedimentation/Seal.purs << 'EOF'
module Noema.Sedimentation.Seal where

import Prelude

-- | 封印: トランザクションの完了証明
-- | 意志が事実として沈殿した証
newtype Seal = Seal
  { success :: Boolean
  , version :: Int
  , hash :: String
  , timestamp :: Number
  }

derive instance eqSeal :: Eq Seal
EOF

# Attractor.purs（抽象）
cat > src/Noema/Sedimentation/Attractor.purs << 'EOF'
module Noema.Sedimentation.Attractor where

import Prelude
import Noema.Sedimentation.Seal (Seal)

-- | Attractor: 意志が沈殿する引き込み域
-- | 力学系における安定点
-- | 具体的な実装は Platform/ で提供
class Attractor a where
  -- | 意志を事実として沈殿させる
  sediment :: forall intent. intent -> a Seal
EOF

echo "=== リファクタリング完了 ==="
echo ""
echo "次のステップ:"
echo "1. spago build でビルド確認"
echo "2. エラーがあれば手動で修正"
echo "3. npm run build で Workers ビルド"
echo "4. git add -A && git commit -m 'refactor: categorical module structure'"
