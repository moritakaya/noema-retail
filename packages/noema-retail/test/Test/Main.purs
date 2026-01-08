-- | Noema Retail Test Main
-- |
-- | 小売実装のテストを実行するエントリーポイント
-- | 基本 Arrow 法則テストは noema-core パッケージで実行
module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

import Test.Laws.ArrowInventory as ArrowInventory

main :: Effect Unit
main = do
  log "╔════════════════════════════════════════════════════════════╗"
  log "║           Noema Retail Test Suite                          ║"
  log "╚════════════════════════════════════════════════════════════╝"
  log ""

  -- InventoryF を使った Arrow 法則
  ArrowInventory.runInventoryTests

  log ""
  log "╔════════════════════════════════════════════════════════════╗"
  log "║           Noema Retail Test Suite Complete                 ║"
  log "╚════════════════════════════════════════════════════════════╝"
