-- | Noema Vocabulary: Item（小売アイテム）
-- |
-- | Thing の Retail 具体化。商品・品目の個体を表現。
-- | すべての変更は Sediment として記録され、イミュータブル。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Item は ThingF の Retail ドメインにおける具体化。
-- | Thing の一般的な構造を継承しつつ、小売固有の属性を定義する。
-- |
-- | ```
-- | ThingF (noema-core)
-- |   │
-- |   └── Item (noema-retail)
-- |       ├── RetailPropertyKey（型安全な属性キー）
-- |       └── ItemCategory（商品分類）
-- | ```
-- |
-- | ## 設計原則
-- |
-- | 1. **situs（位置）**: Item は Subject に包摂され、situs :: SubjectId で参照
-- | 2. **Nomos 非認識**: Item 自体は World を持たない。Subject の World で解釈
-- | 3. **識別子設計**:
-- |    - ThingId = 内部識別子（UUID）
-- |    - SKU/JAN = PropertyKey として格納（検索用インデックス付き）
-- | 4. **イミュータブル**: すべての変更は Sediment として INSERT のみ
-- |
-- | ## 時間構造（Husserl）
-- |
-- | ThingF と同様に三層の時間構造を持つ：
-- | - Retention（把持）: 過去の ItemSnapshot
-- | - Primal（原印象）: 現在の Item 状態
-- | - Protention（予持）: 未来の Pending Intent
module Noema.Vorzeichnung.Vocabulary.Item
  ( -- * RetailPropertyKey（型安全な属性キー）
    RetailPropertyKey(..)
  , toPropertyKey
  , fromPropertyKey
    -- * ItemCategory（商品分類）
  , ItemCategory(..)
    -- * Item（小売アイテム）
  , Item
  , ItemSnapshot
  , ItemEvent(..)
    -- * スマートコンストラクタ
  , mkItem
  , mkItemWithSku
  , getItemSku
  , getItemJan
  , getItemCategory
  ) where

import Prelude

import Data.Argonaut.Core (Json, stringify)
import Data.Argonaut.Encode (encodeJson)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits as SCU
import Noema.Topos.Situs (ThingId, SubjectId, Timestamp)
import Noema.Vorzeichnung.Vocabulary.ThingF
  ( PropertyKey(..)
  , PropertyValue
  , ThingState
  , ThingSnapshot
  , ChangeReason
  )

-- ============================================================
-- RetailPropertyKey（型安全な属性キー）
-- ============================================================

-- | 小売業固有の属性キー
-- |
-- | 型安全性を確保しつつ、PropertyKey への変換を提供。
-- | これにより、タイポによるエラーを防ぎ、
-- | IDE の補完が効くようになる。
-- |
-- | ## 識別子 vs 属性
-- |
-- | - SKU, JAN, Barcode: 識別子として使用（検索用インデックス推奨）
-- | - その他: 属性として使用
-- |
-- | ## 拡張性
-- |
-- | 新しい属性キーが必要な場合：
-- | 1. この型にコンストラクタを追加
-- | 2. toPropertyKey/fromPropertyKey を更新
-- | 3. Nomos.Rules.propertySchema に型制約を追加
data RetailPropertyKey
  -- 識別子（検索キー）
  = SKU                -- ^ Stock Keeping Unit
  | JAN                -- ^ Japanese Article Number (EAN)
  | Barcode            -- ^ バーコード（汎用）
  -- 分類
  | Category           -- ^ 商品カテゴリ
  | Brand              -- ^ ブランド
  | Manufacturer       -- ^ 製造元
  -- 物理属性
  | Color              -- ^ 色
  | Size               -- ^ サイズ
  | Weight             -- ^ 重量（グラム）
  | Dimensions         -- ^ 寸法（JSON: {width, height, depth}）
  -- 期限
  | ExpiryDate         -- ^ 賞味期限/消費期限
  | ManufacturedDate   -- ^ 製造日
  | LotNumber          -- ^ ロット番号
  -- 価格（参考）
  | ListPrice          -- ^ 定価
  | CostPrice          -- ^ 原価
  -- その他
  | Description        -- ^ 説明
  | ImageUrl           -- ^ 画像URL
  | CustomProperty String  -- ^ カスタム属性

derive instance eqRetailPropertyKey :: Eq RetailPropertyKey
derive instance ordRetailPropertyKey :: Ord RetailPropertyKey

instance showRetailPropertyKey :: Show RetailPropertyKey where
  show SKU = "SKU"
  show JAN = "JAN"
  show Barcode = "Barcode"
  show Category = "Category"
  show Brand = "Brand"
  show Manufacturer = "Manufacturer"
  show Color = "Color"
  show Size = "Size"
  show Weight = "Weight"
  show Dimensions = "Dimensions"
  show ExpiryDate = "ExpiryDate"
  show ManufacturedDate = "ManufacturedDate"
  show LotNumber = "LotNumber"
  show ListPrice = "ListPrice"
  show CostPrice = "CostPrice"
  show Description = "Description"
  show ImageUrl = "ImageUrl"
  show (CustomProperty name) = "(CustomProperty " <> show name <> ")"

-- | RetailPropertyKey を PropertyKey に変換
-- |
-- | PropertyKey は文字列ベースなので、
-- | RetailPropertyKey の型安全性を保ちつつ変換する。
toPropertyKey :: RetailPropertyKey -> PropertyKey
toPropertyKey = PropertyKey <<< case _ of
  SKU -> "sku"
  JAN -> "jan"
  Barcode -> "barcode"
  Category -> "category"
  Brand -> "brand"
  Manufacturer -> "manufacturer"
  Color -> "color"
  Size -> "size"
  Weight -> "weight"
  Dimensions -> "dimensions"
  ExpiryDate -> "expiry_date"
  ManufacturedDate -> "manufactured_date"
  LotNumber -> "lot_number"
  ListPrice -> "list_price"
  CostPrice -> "cost_price"
  Description -> "description"
  ImageUrl -> "image_url"
  CustomProperty name -> "custom_" <> String.toLower name

-- | PropertyKey から RetailPropertyKey への変換（可能な場合）
-- |
-- | 認識できない PropertyKey の場合は Nothing を返す。
fromPropertyKey :: PropertyKey -> Maybe RetailPropertyKey
fromPropertyKey (PropertyKey key) = case key of
  "sku" -> Just SKU
  "jan" -> Just JAN
  "barcode" -> Just Barcode
  "category" -> Just Category
  "brand" -> Just Brand
  "manufacturer" -> Just Manufacturer
  "color" -> Just Color
  "size" -> Just Size
  "weight" -> Just Weight
  "dimensions" -> Just Dimensions
  "expiry_date" -> Just ExpiryDate
  "manufactured_date" -> Just ManufacturedDate
  "lot_number" -> Just LotNumber
  "list_price" -> Just ListPrice
  "cost_price" -> Just CostPrice
  "description" -> Just Description
  "image_url" -> Just ImageUrl
  _ -> Nothing  -- 未知のキーまたはカスタム属性

-- ============================================================
-- ItemCategory（商品分類）
-- ============================================================

-- | 商品カテゴリ
-- |
-- | 小売業でよく使用される分類。
-- | Nomos.Rules.propertySchema で EnumType として定義可能。
data ItemCategory
  = Food              -- ^ 食品
  | Beverage          -- ^ 飲料
  | Clothing          -- ^ 衣類
  | Electronics       -- ^ 電化製品
  | Cosmetics         -- ^ 化粧品
  | Medicine          -- ^ 医薬品
  | Household         -- ^ 日用品
  | Stationery        -- ^ 文房具
  | Toys              -- ^ 玩具
  | Other String      -- ^ その他

derive instance eqItemCategory :: Eq ItemCategory

instance showItemCategory :: Show ItemCategory where
  show Food = "Food"
  show Beverage = "Beverage"
  show Clothing = "Clothing"
  show Electronics = "Electronics"
  show Cosmetics = "Cosmetics"
  show Medicine = "Medicine"
  show Household = "Household"
  show Stationery = "Stationery"
  show Toys = "Toys"
  show (Other name) = "(Other " <> show name <> ")"

-- ============================================================
-- Item（小売アイテム）
-- ============================================================

-- | Item: 小売アイテムの現在状態
-- |
-- | ThingState の型エイリアス。
-- | Retail 固有の解釈を持つが、構造は ThingState と同一。
-- |
-- | ## フィールド
-- |
-- | - thingId: 内部識別子（UUID）
-- | - properties: 属性（SKU, JAN, Color 等は PropertyKey で格納）
-- | - situs: 包摂する Subject（倉庫、店舗等）
-- | - lastModified: 最終更新時刻
-- | - protentions: 予定されている Intent の ID 一覧
-- |
-- | ## 識別子について
-- |
-- | ThingId は内部 UUID。SKU/JAN は properties に格納し、
-- | 検索時はインデックスを活用する。
type Item = ThingState

-- | ItemSnapshot: 過去の Item 状態
-- |
-- | ThingSnapshot の型エイリアス。
-- | Retention（把持）で使用される。
type ItemSnapshot = ThingSnapshot

-- ============================================================
-- ItemEvent（イベント）
-- ============================================================

-- | Item の状態変更イベント
-- |
-- | Event Sourcing パターンでの状態変更記録。
-- | Sediment に沈殿する前の「意図」を表現。
-- |
-- | ## 使用シナリオ
-- |
-- | 1. ItemCreated: 新規アイテム登録
-- | 2. PropertyChanged: 属性変更（色、サイズ等）
-- | 3. SitusChanged: 位置変更（倉庫間移動等）
-- | 4. ItemArchived: アイテムのアーカイブ（論理削除）
data ItemEvent
  = ItemCreated
      { thingId :: ThingId
      , initialProperties :: Map PropertyKey PropertyValue
      , situs :: SubjectId
      , createdAt :: Timestamp
      }
  | PropertyChanged
      { thingId :: ThingId
      , key :: RetailPropertyKey
      , oldValue :: PropertyValue
      , newValue :: PropertyValue
      , changedAt :: Timestamp
      }
  | SitusChanged
      { thingId :: ThingId
      , from :: SubjectId
      , to :: SubjectId
      , reason :: ChangeReason
      , changedAt :: Timestamp
      }
  | ItemArchived
      { thingId :: ThingId
      , archivedAt :: Timestamp
      , reason :: String
      }

derive instance eqItemEvent :: Eq ItemEvent

instance showItemEvent :: Show ItemEvent where
  show (ItemCreated r) = "(ItemCreated " <> show r.thingId <> ")"
  show (PropertyChanged r) = "(PropertyChanged " <> show r.thingId <> " " <> show r.key <> ")"
  show (SitusChanged r) = "(SitusChanged " <> show r.thingId <> " " <> show r.from <> " -> " <> show r.to <> ")"
  show (ItemArchived r) = "(ItemArchived " <> show r.thingId <> ")"

-- ============================================================
-- スマートコンストラクタ
-- ============================================================

-- | Item を作成
-- |
-- | 必須フィールドのみで Item を作成。
-- | 属性は後から setProperty で追加可能。
mkItem
  :: ThingId
  -> SubjectId
  -> Timestamp
  -> Item
mkItem tid situs ts =
  { thingId: tid
  , properties: Map.empty
  , situs: situs
  , lastModified: ts
  , protentions: []
  }

-- | SKU 付きで Item を作成
-- |
-- | 小売業では SKU が必須のことが多いため、
-- | SKU を指定して Item を作成するヘルパー。
mkItemWithSku
  :: ThingId
  -> String       -- ^ SKU
  -> SubjectId
  -> Timestamp
  -> Item
mkItemWithSku tid sku situs ts =
  { thingId: tid
  , properties: Map.singleton (toPropertyKey SKU) (encodeJson sku)
  , situs: situs
  , lastModified: ts
  , protentions: []
  }

-- | Item から SKU を取得
-- |
-- | SKU が設定されていない場合は Nothing。
getItemSku :: Item -> Maybe String
getItemSku item =
  Map.lookup (toPropertyKey SKU) item.properties >>= decodeString

-- | Item から JAN を取得
getItemJan :: Item -> Maybe String
getItemJan item =
  Map.lookup (toPropertyKey JAN) item.properties >>= decodeString

-- | Item からカテゴリを取得
getItemCategory :: Item -> Maybe String
getItemCategory item =
  Map.lookup (toPropertyKey Category) item.properties >>= decodeString

-- ============================================================
-- 内部ヘルパー
-- ============================================================

-- | JSON 文字列をデコード（簡易版）
-- |
-- | JSON が文字列の場合、クォートを除去して返す。
-- | null や非文字列の場合は Nothing。
decodeString :: Json -> Maybe String
decodeString json =
  let str = stringify json
  in if str == "null" then Nothing
     else Just (removeQuotes str)
  where
    removeQuotes :: String -> String
    removeQuotes s =
      let len = SCU.length s
      in if len >= 2 && SCU.take 1 s == "\"" && SCU.takeRight 1 s == "\""
         then SCU.drop 1 (SCU.dropRight 1 s)
         else s
