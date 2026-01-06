module Noema.Vorzeichnung.Vocabulary.RetailF where

import Prelude
import Data.Functor.Coproduct (Coproduct)

import Noema.Vorzeichnung.Vocabulary.InventoryF (InventoryF)
import Noema.Vorzeichnung.Vocabulary.HttpF (HttpF)
import Noema.Vorzeichnung.Vocabulary.StorageF (StorageF)

-- | 語彙の余積 = Noema の「意志のアルファベット」
-- | 圏論的には: RetailF = InventoryF + HttpF + StorageF
type RetailF = Coproduct InventoryF (Coproduct HttpF StorageF)
