-- | Noema Test Main
-- |
-- | 全てのテストを実行するエントリーポイント
module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

import Test.Laws.Arrow as Arrow
import Test.Laws.ArrowInventory as ArrowInventory

main :: Effect Unit
main = do
  log "╔════════════════════════════════════════════════════════════╗"
  log "║           Noema Arrow Laws Test Suite                      ║"
  log "╚════════════════════════════════════════════════════════════╝"
  log ""
  
  -- 基本 Arrow 法則
  Arrow.main
  
  log ""
  log "────────────────────────────────────────────────────────────"
  log ""
  
  -- InventoryF を使った Arrow 法則
  ArrowInventory.runInventoryTests
  
  log ""
  log "╔════════════════════════════════════════════════════════════╗"
  log "║           Test Suite Complete                              ║"
  log "╚════════════════════════════════════════════════════════════╝"
