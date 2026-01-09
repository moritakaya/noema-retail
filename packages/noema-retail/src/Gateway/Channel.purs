-- | Gateway.Channel
-- |
-- | 小売業ドメインのチャネル定義。
-- | 各チャネルは外部システム（POS、EC サイト、決済等）を表す。
module Gateway.Channel where

import Prelude

-- | Channel 圏の対象
-- | Inventory は Presheaf: Channel^op → Set として表現される。
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
