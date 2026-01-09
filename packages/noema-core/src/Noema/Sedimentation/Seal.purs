-- | Noema Sedimentation: Seal（封印）
-- |
-- | トランザクションの完了証明。
-- | 意志が事実として沈殿した証。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Sedimentation（沈殿）の最終形態。
-- | Intent → Interpretation → Factum → Attractor.sediment → Seal
-- |
-- | ## 哲学的基盤
-- |
-- | Seal は「封印」を意味する。
-- | 一度 Seal されたら、その事実は不変となる。
-- | これは Noema の核心原則「Sediment は不変」を型で表現する。
-- |
-- | ## World の記録
-- |
-- | Seal には沈殿時の World（法座標）が記録される。
-- | これにより、「どの法の下で事実となったか」を追跡できる。
-- | 将来の Nomos 改訂時に、この情報が Connection 検証に使用される。
module Noema.Sedimentation.Seal
  ( Seal(..)
  , mkSeal
  ) where

import Prelude

import Noema.Topos.Situs (SedimentId, Timestamp)
import Noema.Topos.Nomos (World)

-- | Seal: 沈殿の封印（トランザクションの完了証明）
-- |
-- | 意志が事実として沈殿した証。
-- | 一度 Seal されたら不変。
-- |
-- | ## フィールド
-- |
-- | - success: 沈殿が成功したか
-- | - sedimentId: Lamport Clock による沈殿 ID
-- | - hash: 内容のハッシュ（整合性検証用）
-- | - timestamp: 沈殿時刻
-- | - world: 適用された法（Nomos バージョンを含む）
-- |
-- | ## 重要
-- |
-- | world フィールドにより、Seal が「どの法の下で作成されたか」が記録される。
-- | これは将来の Nomos 改訂時に重要な情報となる：
-- | - 既存の Seal は旧法の下で有効
-- | - 新しい Intent は附則に従って処理
newtype Seal = Seal
  { success :: Boolean         -- 沈殿が成功したか
  , sedimentId :: SedimentId   -- Lamport Clock
  , hash :: String             -- 内容のハッシュ
  , timestamp :: Timestamp     -- 沈殿時刻
  , world :: World             -- 適用された法（重要！）
  }

derive instance eqSeal :: Eq Seal

instance showSeal :: Show Seal where
  show (Seal s) = "(Seal " <> show s.sedimentId <> " " <> show s.world.nomosVersion <> ")"

-- | Seal を作成
-- |
-- | Attractor の sediment 関数内で使用される。
-- | world には沈殿時点の Attractor の World を指定する。
mkSeal
  :: Boolean
  -> SedimentId
  -> String
  -> Timestamp
  -> World
  -> Seal
mkSeal success sid hash ts world = Seal
  { success
  , sedimentId: sid
  , hash
  , timestamp: ts
  , world
  }
