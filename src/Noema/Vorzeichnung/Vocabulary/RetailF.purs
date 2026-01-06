-- | Noema Vocabulary: RetailF（余積）
-- |
-- | 全ての語彙を統合した余積型。
-- | Noema の「意志のアルファベット」を構成する。
-- |
-- | 圏論的構造:
-- | RetailF = InventoryF + HttpF + StorageF
-- |
-- | 単項関手の余積として定義。
module Noema.Vorzeichnung.Vocabulary.RetailF
  ( RetailF
  , RetailIntent
  -- Injection
  , inInventory
  , inHttp
  , inStorage
  -- Intent lifting
  , liftInventory
  , liftHttp
  , liftStorage
  ) where

import Prelude

import Data.Functor.Coproduct (Coproduct, left, right)

import Noema.Vorzeichnung.Intent (Intent, hoistIntent)
import Noema.Vorzeichnung.Vocabulary.InventoryF (InventoryF)
import Noema.Vorzeichnung.Vocabulary.HttpF (HttpF)
import Noema.Vorzeichnung.Vocabulary.StorageF (StorageF)

-- ============================================================
-- RetailF: 語彙の余積
-- ============================================================

-- | 語彙の余積 = Noema の「意志のアルファベット」
-- |
-- | 圏論的には:
-- | RetailF a = InventoryF a + HttpF a + StorageF a
-- |
-- | Coproduct の入れ子で表現:
-- | RetailF = Coproduct InventoryF (Coproduct HttpF StorageF)
type RetailF = Coproduct InventoryF (Coproduct HttpF StorageF)

-- ============================================================
-- Intent 型
-- ============================================================

-- | Retail Intent の型
type RetailIntent a b = Intent RetailF a b

-- ============================================================
-- Injection 関数
-- ============================================================

-- | InventoryF を RetailF に injection
inInventory :: InventoryF ~> RetailF
inInventory = left

-- | HttpF を RetailF に injection
inHttp :: HttpF ~> RetailF
inHttp = right <<< left

-- | StorageF を RetailF に injection
inStorage :: StorageF ~> RetailF
inStorage = right <<< right

-- ============================================================
-- Intent lifting
-- ============================================================

-- | InventoryIntent を RetailIntent に持ち上げ
-- |
-- | ```purescript
-- | inventoryOp :: Intent InventoryF Unit StockInfo
-- | retailOp :: RetailIntent Unit StockInfo
-- | retailOp = liftInventory inventoryOp
-- | ```
liftInventory :: forall a b. Intent InventoryF a b -> RetailIntent a b
liftInventory = hoistIntent inInventory

-- | HttpIntent を RetailIntent に持ち上げ
liftHttp :: forall a b. Intent HttpF a b -> RetailIntent a b
liftHttp = hoistIntent inHttp

-- | StorageIntent を RetailIntent に持ち上げ
liftStorage :: forall a b. Intent StorageF a b -> RetailIntent a b
liftStorage = hoistIntent inStorage

-- ============================================================
-- Handler の構成
-- ============================================================

-- | RetailF の Handler は各コンポーネントの Handler の組み合わせ:
-- |
-- | ```purescript
-- | retailHandler :: RetailF ~> Effect
-- | retailHandler = coproduct inventoryHandler (coproduct httpHandler storageHandler)
-- | ```
-- |
-- | これは余積の普遍性により導かれる:
-- | [h1, h2, h3] : F1 + F2 + F3 → G
-- | where h1 : F1 → G, h2 : F2 → G, h3 : F3 → G
