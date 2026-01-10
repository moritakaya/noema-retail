-- | Noema Item Test
-- |
-- | Item（小売アイテム）モジュールのテスト。
-- |
-- | ## テスト対象
-- |
-- | - RetailPropertyKey の変換
-- | - ItemCategory の等値性・Show
-- | - Item の作成・属性取得
-- | - ItemEvent の構造
module Test.Item where

import Prelude

import Data.Argonaut.Encode (encodeJson)
import Data.Foldable (and)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, isNothing)
import Effect (Effect)
import Effect.Console (log)

import Noema.Topos.Situs (Timestamp(..), mkThingId, mkSubjectId)
import Noema.Vorzeichnung.Vocabulary.ThingF (PropertyKey(..), getReasonType)
import Noema.Vorzeichnung.Vocabulary.RetailChangeReason (RetailChangeReason(..), toChangeReason)
import Noema.Vorzeichnung.Vocabulary.Item
  ( RetailPropertyKey(..)
  , ItemCategory(..)
  , ItemEvent(..)
  , toPropertyKey
  , fromPropertyKey
  , mkItem
  , mkItemWithSku
  , getItemSku
  , getItemJan
  )

-- ============================================================
-- RetailPropertyKey テスト
-- ============================================================

-- | RetailPropertyKey → PropertyKey 変換
test_retail_property_key_to_property_key :: Effect Boolean
test_retail_property_key_to_property_key = do
  let
    results =
      [ toPropertyKey SKU == PropertyKey "sku"
      , toPropertyKey JAN == PropertyKey "jan"
      , toPropertyKey Color == PropertyKey "color"
      , toPropertyKey Size == PropertyKey "size"
      , toPropertyKey ExpiryDate == PropertyKey "expiry_date"
      , toPropertyKey (CustomProperty "MyAttr") == PropertyKey "custom_myattr"
      ]

  pure (and results)

-- | PropertyKey → RetailPropertyKey 変換
test_property_key_to_retail_property_key :: Effect Boolean
test_property_key_to_retail_property_key = do
  let
    results =
      [ fromPropertyKey (PropertyKey "sku") == Just SKU
      , fromPropertyKey (PropertyKey "jan") == Just JAN
      , fromPropertyKey (PropertyKey "color") == Just Color
      , fromPropertyKey (PropertyKey "expiry_date") == Just ExpiryDate
      , isNothing (fromPropertyKey (PropertyKey "unknown_key"))
      ]

  pure (and results)

-- | RetailPropertyKey の等値性
test_retail_property_key_equality :: Effect Boolean
test_retail_property_key_equality = do
  let
    results =
      [ SKU == SKU
      , SKU /= JAN
      , CustomProperty "A" == CustomProperty "A"
      , CustomProperty "A" /= CustomProperty "B"
      ]

  pure (and results)

-- | RetailPropertyKey の順序
test_retail_property_key_ordering :: Effect Boolean
test_retail_property_key_ordering = do
  -- 順序は derive による（コンストラクタ定義順）
  pure $ SKU < JAN && JAN < Barcode && Color < Size

-- | RetailPropertyKey の Show
test_retail_property_key_show :: Effect Boolean
test_retail_property_key_show = do
  let
    results =
      [ show SKU == "SKU"
      , show JAN == "JAN"
      , show Color == "Color"
      , show (CustomProperty "Test") == "(CustomProperty \"Test\")"
      ]

  pure (and results)

-- ============================================================
-- ItemCategory テスト
-- ============================================================

-- | ItemCategory の等値性
test_item_category_equality :: Effect Boolean
test_item_category_equality = do
  let
    results =
      [ Food == Food
      , Food /= Beverage
      , Other "X" == Other "X"
      , Other "X" /= Other "Y"
      ]

  pure (and results)

-- | ItemCategory の Show
test_item_category_show :: Effect Boolean
test_item_category_show = do
  let
    results =
      [ show Food == "Food"
      , show Beverage == "Beverage"
      , show Electronics == "Electronics"
      , show (Other "Custom") == "(Other \"Custom\")"
      ]

  pure (and results)

-- ============================================================
-- Item 作成テスト
-- ============================================================

-- | mkItem でItem を作成
test_mk_item :: Effect Boolean
test_mk_item = do
  let
    tid = mkThingId "item-001"
    sid = mkSubjectId "warehouse-001"
    ts = Timestamp 1704067200000.0

    item = mkItem tid sid ts

  pure $
    item.thingId == tid &&
    item.situs == sid &&
    item.lastModified == ts &&
    Map.isEmpty item.properties &&
    item.protentions == []

-- | mkItemWithSku で SKU 付き Item を作成
test_mk_item_with_sku :: Effect Boolean
test_mk_item_with_sku = do
  let
    tid = mkThingId "item-002"
    sku = "ABC-12345"
    sid = mkSubjectId "store-001"
    ts = Timestamp 1704153600000.0

    item = mkItemWithSku tid sku sid ts

  pure $
    item.thingId == tid &&
    item.situs == sid &&
    Map.size item.properties == 1 &&
    isJust (Map.lookup (toPropertyKey SKU) item.properties)

-- | getItemSku で SKU を取得
test_get_item_sku :: Effect Boolean
test_get_item_sku = do
  let
    tid = mkThingId "item-003"
    sku = "XYZ-67890"
    sid = mkSubjectId "store-002"
    ts = Timestamp 1704240000000.0

    item = mkItemWithSku tid sku sid ts
    retrievedSku = getItemSku item

  pure $ retrievedSku == Just sku

-- | SKU なしの Item から getItemSku
test_get_item_sku_empty :: Effect Boolean
test_get_item_sku_empty = do
  let
    item = mkItem (mkThingId "item-004") (mkSubjectId "warehouse-002") (Timestamp 0.0)

  pure $ isNothing (getItemSku item)

-- | getItemJan で JAN を取得
test_get_item_jan :: Effect Boolean
test_get_item_jan = do
  let
    tid = mkThingId "item-005"
    sid = mkSubjectId "store-003"
    ts = Timestamp 1704326400000.0

    -- JAN を手動で設定
    item = mkItem tid sid ts
    itemWithJan = item { properties = Map.singleton (toPropertyKey JAN) (encodeJson "4901234567890") }

    retrievedJan = getItemJan itemWithJan

  pure $ retrievedJan == Just "4901234567890"

-- ============================================================
-- ItemEvent テスト
-- ============================================================

-- | ItemCreated イベント
test_item_event_created :: Effect Boolean
test_item_event_created = do
  let
    tid = mkThingId "item-006"
    sid = mkSubjectId "warehouse-003"
    ts = Timestamp 1704412800000.0

    event = ItemCreated
      { thingId: tid
      , initialProperties: Map.empty
      , situs: sid
      , createdAt: ts
      }

  pure $ case event of
    ItemCreated r -> r.thingId == tid && r.situs == sid
    _ -> false

-- | PropertyChanged イベント
test_item_event_property_changed :: Effect Boolean
test_item_event_property_changed = do
  let
    tid = mkThingId "item-007"
    ts = Timestamp 1704499200000.0

    event = PropertyChanged
      { thingId: tid
      , key: Color
      , oldValue: encodeJson "red"
      , newValue: encodeJson "blue"
      , changedAt: ts
      }

  pure $ case event of
    PropertyChanged r -> r.key == Color
    _ -> false

-- | SitusChanged イベント
test_item_event_situs_changed :: Effect Boolean
test_item_event_situs_changed = do
  let
    tid = mkThingId "item-008"
    from = mkSubjectId "warehouse-001"
    to = mkSubjectId "store-001"
    ts = Timestamp 1704585600000.0
    transferReason = toChangeReason Transfer

    event = SitusChanged
      { thingId: tid
      , from: from
      , to: to
      , reason: transferReason
      , changedAt: ts
      }

  pure $ case event of
    SitusChanged r -> r.from == from && r.to == to && getReasonType r.reason == "transfer"
    _ -> false

-- | ItemEvent の Show
test_item_event_show :: Effect Boolean
test_item_event_show = do
  let
    tid = mkThingId "item-009"
    sid = mkSubjectId "warehouse-004"
    ts = Timestamp 1704672000000.0

    event = ItemCreated
      { thingId: tid
      , initialProperties: Map.empty
      , situs: sid
      , createdAt: ts
      }

    shown = show event

  -- ThingId は newtype なので Show は String を継承 → "\"item-009\""
  pure $ shown == "(ItemCreated \"item-009\")"

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema Item Test ==="
  log ""

  log "--- RetailPropertyKey ---"

  log "toPropertyKey conversion"
  r1 <- test_retail_property_key_to_property_key
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log "fromPropertyKey conversion"
  r2 <- test_property_key_to_retail_property_key
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log "RetailPropertyKey equality"
  r3 <- test_retail_property_key_equality
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log "RetailPropertyKey ordering"
  r4 <- test_retail_property_key_ordering
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log "RetailPropertyKey show"
  r5 <- test_retail_property_key_show
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ItemCategory ---"

  log "ItemCategory equality"
  r6 <- test_item_category_equality
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log "ItemCategory show"
  r7 <- test_item_category_show
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Item creation ---"

  log "mkItem"
  r8 <- test_mk_item
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log "mkItemWithSku"
  r9 <- test_mk_item_with_sku
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log "getItemSku"
  r10 <- test_get_item_sku
  log $ "  Result: " <> if r10 then "✓ PASS" else "✗ FAIL"

  log "getItemSku (empty)"
  r11 <- test_get_item_sku_empty
  log $ "  Result: " <> if r11 then "✓ PASS" else "✗ FAIL"

  log "getItemJan"
  r12 <- test_get_item_jan
  log $ "  Result: " <> if r12 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ItemEvent ---"

  log "ItemCreated event"
  r13 <- test_item_event_created
  log $ "  Result: " <> if r13 then "✓ PASS" else "✗ FAIL"

  log "PropertyChanged event"
  r14 <- test_item_event_property_changed
  log $ "  Result: " <> if r14 then "✓ PASS" else "✗ FAIL"

  log "SitusChanged event"
  r15 <- test_item_event_situs_changed
  log $ "  Result: " <> if r15 then "✓ PASS" else "✗ FAIL"

  log "ItemEvent show"
  r16 <- test_item_event_show
  log $ "  Result: " <> if r16 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = and [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16]
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
