-- | Noema Retail: 在庫（Inventory）ドメイン
-- |
-- | 在庫の状態と変動を定義する。
-- |
-- | 圏論的構造：
-- | - Inventory は Channel^op → Set の関手（presheaf）
-- | - 各チャネルから見た在庫数を統一的に管理
-- | - 在庫変動はイベントソーシングで追跡
-- |
-- | 特徴：
-- | - Single Source of Truth: Noema が在庫の真実
-- | - 多チャネル同期: 楽天、Yahoo、スマレジ、自社EC
-- | - イベント駆動: 変動はすべてログに記録
module Noema.Vorzeichnung.Vocabulary.InventoryF
  ( -- 在庫
    Inventory(..)
  , InventoryRecord
  , InventoryId(..)
  , Quantity(..)
  , QuantityDelta(..)
  -- 在庫イベント
  , InventoryEvent(..)
  , InventoryEventRecord
  , InventoryEventType(..)
  , InventoryLogEntry(..)
  , InventoryLogEntryRecord
  -- チャネル
  , Channel(..)
  , ChannelSyncStatus(..)
  , ChannelSyncStatusRecord
  , SyncStatus(..)
  , SyncResult(..)
  -- 予約
  , Reservation(..)
  , ReservationRecord
  , ReservationId(..)
  -- ロケーション
  , InventoryLocation(..)
  , InventoryLocationRecord
  , LocationType(..)
  -- DSL 操作
  , InventoryF(..)
  -- ユーティリティ
  , availableQuantity
  , applyDelta
  , channelToString
  , channelFromString
  , eventTypeToString
  , eventTypeFromString
  , syncStatusToString
  , syncStatusFromString
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)

import Noema.Vorzeichnung.Vocabulary.Base (ThingId, Timestamp, LocationId)

--------------------------------------------------------------------------------
-- 基本型
--------------------------------------------------------------------------------

-- | 在庫ID
newtype InventoryId = InventoryId String

derive instance Newtype InventoryId _
derive instance Eq InventoryId
derive instance Ord InventoryId
derive newtype instance Show InventoryId

-- | 数量
newtype Quantity = Quantity Int

derive instance Newtype Quantity _
derive instance Eq Quantity
derive instance Ord Quantity
derive newtype instance Show Quantity
derive newtype instance Semiring Quantity

-- | 数量変動（正は増加、負は減少）
newtype QuantityDelta = QuantityDelta Int

derive instance Newtype QuantityDelta _
derive instance Eq QuantityDelta
derive newtype instance Show QuantityDelta

--------------------------------------------------------------------------------
-- チャネル
--------------------------------------------------------------------------------

-- | 販売チャネル
-- |
-- | 圏論的解釈：
-- | Channel は離散圏の対象。
-- | Inventory : Channel^op → Set は presheaf。
data Channel
  = ChannelRakuten       -- 楽天市場
  | ChannelYahoo         -- Yahoo!ショッピング
  | ChannelSmaregi       -- スマレジ（実店舗）
  | ChannelSelfEC        -- 自社EC
  | ChannelStripe        -- Stripe（決済）
  | ChannelOther String  -- その他（拡張用）

derive instance Generic Channel _
derive instance Eq Channel
derive instance Ord Channel
instance Show Channel where show = genericShow

-- | チャネルの識別子文字列
channelToString :: Channel -> String
channelToString = case _ of
  ChannelRakuten -> "rakuten"
  ChannelYahoo -> "yahoo"
  ChannelSmaregi -> "smaregi"
  ChannelSelfEC -> "self_ec"
  ChannelStripe -> "stripe"
  ChannelOther s -> s

-- | 文字列からチャネルへ
channelFromString :: String -> Channel
channelFromString = case _ of
  "rakuten" -> ChannelRakuten
  "yahoo" -> ChannelYahoo
  "smaregi" -> ChannelSmaregi
  "self_ec" -> ChannelSelfEC
  "stripe" -> ChannelStripe
  s -> ChannelOther s

--------------------------------------------------------------------------------
-- 在庫
--------------------------------------------------------------------------------

-- | 在庫
-- |
-- | 特定の商品・ロケーションにおける在庫状態。
-- |
-- | 圏論的解釈：
-- | Inventory(product, location) は在庫数の「現在値」を表す。
-- | これは Vorzeichnungsschema が実行（忘却）された結果の一部。
type InventoryRecord =
  { id :: InventoryId
  , productId :: ThingId            -- 商品（Thing）への参照
  , locationId :: LocationId        -- 在庫ロケーション
  , quantity :: Quantity            -- 総在庫数
  , reserved :: Quantity            -- 予約済み数量
  , updatedAt :: Timestamp
  }

newtype Inventory = Inventory InventoryRecord

derive instance Newtype Inventory _
derive instance Generic Inventory _
instance Show Inventory where show = genericShow

-- | 販売可能数量
-- |
-- | available = quantity - reserved
availableQuantity :: Inventory -> Quantity
availableQuantity (Inventory inv) = Quantity (q - r)
  where
    Quantity q = inv.quantity
    Quantity r = inv.reserved

-- | 在庫ロケーション
type InventoryLocationRecord =
  { id :: LocationId
  , name :: String
  , locationType :: LocationType
  , channel :: Maybe Channel        -- チャネル固有のロケーション（店舗など）
  }

newtype InventoryLocation = InventoryLocation InventoryLocationRecord

derive instance Newtype InventoryLocation _
derive instance Generic InventoryLocation _
instance Show InventoryLocation where show = genericShow

data LocationType
  = LTWarehouse         -- 倉庫
  | LTStore             -- 店舗
  | LTVirtual           -- 仮想（デジタル商品）

derive instance Generic LocationType _
derive instance Eq LocationType
instance Show LocationType where show = genericShow

--------------------------------------------------------------------------------
-- 在庫イベント
--------------------------------------------------------------------------------

-- | 在庫イベント
-- |
-- | 在庫の変動を表すイベント。
-- | イベントソーシングの基盤。
-- |
-- | 圏論的解釈：
-- | InventoryEvent は Inventory 圏の射。
-- | apply : InventoryEvent × Inventory → Inventory
type InventoryEventRecord =
  { eventType :: InventoryEventType
  , productId :: ThingId
  , locationId :: LocationId
  , channel :: Channel              -- イベント発生元チャネル
  , delta :: QuantityDelta          -- 数量変動
  , referenceId :: Maybe String     -- 注文ID等
  , timestamp :: Timestamp
  , metadata :: Maybe String        -- 追加情報（JSON）
  }

newtype InventoryEvent = InventoryEvent InventoryEventRecord

derive instance Newtype InventoryEvent _
derive instance Generic InventoryEvent _
instance Show InventoryEvent where show = genericShow

-- | イベントタイプ
data InventoryEventType
  = IETSale             -- 販売（減少）
  | IETPurchase         -- 仕入れ（増加）
  | IETAdjust           -- 調整（棚卸など）
  | IETTransfer         -- 移動（ロケーション間）
  | IETReserve          -- 予約（available減少）
  | IETRelease          -- 予約解除
  | IETReturn           -- 返品（増加）

derive instance Generic InventoryEventType _
derive instance Eq InventoryEventType
instance Show InventoryEventType where show = genericShow

eventTypeToString :: InventoryEventType -> String
eventTypeToString = case _ of
  IETSale -> "sale"
  IETPurchase -> "purchase"
  IETAdjust -> "adjust"
  IETTransfer -> "transfer"
  IETReserve -> "reserve"
  IETRelease -> "release"
  IETReturn -> "return"

eventTypeFromString :: String -> Maybe InventoryEventType
eventTypeFromString = case _ of
  "sale" -> Just IETSale
  "purchase" -> Just IETPurchase
  "adjust" -> Just IETAdjust
  "transfer" -> Just IETTransfer
  "reserve" -> Just IETReserve
  "release" -> Just IETRelease
  "return" -> Just IETReturn
  _ -> Nothing

-- | 在庫ログエントリ
type InventoryLogEntryRecord =
  { id :: String
  , event :: InventoryEvent
  , quantityBefore :: Quantity
  , quantityAfter :: Quantity
  , createdAt :: Timestamp
  }

newtype InventoryLogEntry = InventoryLogEntry InventoryLogEntryRecord

derive instance Newtype InventoryLogEntry _
derive instance Generic InventoryLogEntry _
instance Show InventoryLogEntry where show = genericShow

-- | 在庫変動を適用
applyDelta :: QuantityDelta -> Quantity -> Quantity
applyDelta (QuantityDelta d) (Quantity q) = Quantity (q + d)

--------------------------------------------------------------------------------
-- チャネル同期
--------------------------------------------------------------------------------

-- | チャネル同期状態
type ChannelSyncStatusRecord =
  { productId :: ThingId
  , channel :: Channel
  , localQuantity :: Quantity       -- Noema側の認識
  , remoteQuantity :: Maybe Quantity -- チャネル側の認識
  , syncStatus :: SyncStatus
  , lastSyncAt :: Maybe Timestamp
  , lastError :: Maybe String
  }

newtype ChannelSyncStatus = ChannelSyncStatus ChannelSyncStatusRecord

derive instance Newtype ChannelSyncStatus _
derive instance Generic ChannelSyncStatus _
instance Show ChannelSyncStatus where show = genericShow

-- | 同期状態
data SyncStatus
  = SSynced             -- 同期済み
  | SPending            -- 同期待ち
  | SError              -- エラー
  | SConflict           -- コンフリクト（手動解決必要）

derive instance Generic SyncStatus _
derive instance Eq SyncStatus
instance Show SyncStatus where show = genericShow

syncStatusToString :: SyncStatus -> String
syncStatusToString = case _ of
  SSynced -> "synced"
  SPending -> "pending"
  SError -> "error"
  SConflict -> "conflict"

syncStatusFromString :: String -> Maybe SyncStatus
syncStatusFromString = case _ of
  "synced" -> Just SSynced
  "pending" -> Just SPending
  "error" -> Just SError
  "conflict" -> Just SConflict
  _ -> Nothing

-- | 同期結果
data SyncResult
  = SyncSuccess
      { channel :: Channel
      , quantitySynced :: Quantity
      , timestamp :: Timestamp
      }
  | SyncFailure
      { channel :: Channel
      , error :: String
      , timestamp :: Timestamp
      }
  | SyncConflict
      { channel :: Channel
      , localQuantity :: Quantity
      , remoteQuantity :: Quantity
      , timestamp :: Timestamp
      }

derive instance Generic SyncResult _
instance Show SyncResult where show = genericShow

--------------------------------------------------------------------------------
-- 予約
--------------------------------------------------------------------------------

-- | 予約ID
newtype ReservationId = ReservationId String

derive instance Newtype ReservationId _
derive instance Eq ReservationId
derive instance Ord ReservationId
derive newtype instance Show ReservationId

-- | 在庫予約
-- |
-- | 注文確定前に在庫を確保するための予約。
-- | 予約中は available が減少する。
type ReservationRecord =
  { id :: ReservationId
  , inventoryId :: InventoryId
  , quantity :: Quantity
  , orderId :: Maybe String         -- 関連する注文ID
  , channel :: Channel
  , expiresAt :: Timestamp          -- 予約期限
  , createdAt :: Timestamp
  }

newtype Reservation = Reservation ReservationRecord

derive instance Newtype Reservation _
derive instance Generic Reservation _
instance Show Reservation where show = genericShow

--------------------------------------------------------------------------------
-- DSL 操作（Functor）
--------------------------------------------------------------------------------

-- | 在庫に関する操作
-- |
-- | Vorzeichnungsschema の語彙。
-- | InventoryF は在庫操作の Intent を構成する。
-- |
-- | 圏論的解釈：
-- | InventoryF は Arrow Effects の制約に従い、
-- | 操作は線形な列（sequence）として設計されている。
-- | 分岐は許可されない。
data InventoryF next
  -- 在庫CRUD
  = GetInventory ThingId LocationId (Maybe Inventory -> next)
  | GetInventoryByProduct ThingId (Array Inventory -> next)
  | CreateInventory ThingId LocationId Quantity (Inventory -> next)
  -- 在庫変動
  | AdjustStock ThingId LocationId QuantityDelta InventoryEventType Channel String (Inventory -> next)
  -- 予約
  | ReserveStock ThingId LocationId Quantity Channel (Maybe String) (Maybe ReservationId -> next)
  | ReleaseReservation ReservationId (Boolean -> next)
  | GetReservation ReservationId (Maybe Reservation -> next)
  -- チャネル同期
  | SyncToChannel ThingId Channel (SyncResult -> next)
  | SyncFromChannel ThingId Channel (SyncResult -> next)
  | SyncAllChannels ThingId (Array SyncResult -> next)
  | GetSyncStatus ThingId (Array ChannelSyncStatus -> next)
  -- ログ
  | GetInventoryLog ThingId Timestamp Timestamp (Array InventoryLogEntry -> next)
  -- バルク操作
  | BulkGetInventory (Array ThingId) (Array Inventory -> next)
  | BulkSyncAllChannels (Array ThingId) (Array { productId :: ThingId, results :: Array SyncResult } -> next)

derive instance Functor InventoryF
