-- | Noema.Horizont.InventoryCarrier
-- |
-- | 在庫管理用 Carrier 型クラス。
-- | noema-core の Carrier を継承し、在庫固有のメソッドを追加。
-- |
-- | 圏論的解釈：
-- | InventoryCarrier は Channel^op → Set として機能する。
-- | 各チャネルの在庫データを Noema 統一形式に変換する自然変換。
-- | Horizont（地平線）を越えて外部在庫データを担う。
module Noema.Horizont.InventoryCarrier
  ( class InventoryCarrier
  , channel
  , getStock
  , setStock
  , syncToNoema
  , syncFromNoema
  , processOrders
  -- Types
  , SyncResult(..)
  , InventoryEvent(..)
  , StockInfo
  , OrderInfo
  ) where

import Prelude

import Data.Either (Either)
import Data.Maybe (Maybe)
import Effect.Aff (Aff)
import Noema.Topos.Situs (ThingId, Quantity, Timestamp)
import Noema.Horizont.Channel (Channel)
import Noema.Horizont.Carrier (class Carrier, CarrierError)

-- | 同期結果
data SyncResult
  = SyncSuccess { channel :: Channel, quantity :: Quantity }
  | SyncFailure { channel :: Channel, error :: String }

derive instance eqSyncResult :: Eq SyncResult

-- | 在庫イベント型
-- |
-- | チャネルからの注文処理で生成されるイベント
data InventoryEvent
  = SaleEvent ThingId Quantity
  | ReturnEvent ThingId Quantity
  | AdjustEvent ThingId Quantity

-- | 在庫情報
type StockInfo =
  { productId :: String
  , quantity :: Int
  , lastUpdated :: Maybe Timestamp
  }

-- | 注文情報
type OrderInfo =
  { orderId :: String
  , items :: Array { productId :: String, quantity :: Int }
  , orderDate :: Timestamp
  , channel :: Channel
  }

-- | 在庫用 Carrier 型クラス
-- |
-- | Carrier を継承し、在庫固有のメソッドを追加。
-- | 各チャネル（楽天、スマレジ等）はこのインターフェースを実装する。
-- | Horizont（地平線）を越えて外部在庫システムと接続する。
class Carrier a <= InventoryCarrier a where
  -- | この Carrier が対応するチャネル
  channel :: a -> Channel

  -- | チャネルから在庫を取得（地平線を越えて外部データを担う）
  getStock :: a -> ThingId -> Aff (Either CarrierError StockInfo)

  -- | チャネルの在庫を更新（地平線を越えて外部へ反映）
  setStock :: a -> ThingId -> Quantity -> Aff (Either CarrierError Unit)

  -- | チャネル → Noema への同期
  syncToNoema :: a -> ThingId -> Aff SyncResult

  -- | Noema → チャネルへの同期
  syncFromNoema :: a -> ThingId -> Quantity -> Aff SyncResult

  -- | 新規注文を処理して在庫イベントを生成
  processOrders :: a -> Timestamp -> Aff { processed :: Int, errors :: Array String, events :: Array InventoryEvent }
