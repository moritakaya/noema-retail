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
