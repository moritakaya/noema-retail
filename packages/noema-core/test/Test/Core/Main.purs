-- | Noema Core Test Main
module Test.Core.Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Test.Laws.Arrow as Arrow

main :: Effect Unit
main = do
  log "╔════════════════════════════════════════════════════════════╗"
  log "║           Noema Core Arrow Laws Test Suite                 ║"
  log "╚════════════════════════════════════════════════════════════╝"
  log ""
  Arrow.main
  log ""
  log "╔════════════════════════════════════════════════════════════╗"
  log "║           Noema Core Test Suite Complete                   ║"
  log "╚════════════════════════════════════════════════════════════╝"
