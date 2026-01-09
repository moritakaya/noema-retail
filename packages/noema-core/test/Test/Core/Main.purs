-- | Noema Core Test Main
module Test.Core.Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Test.Laws.Arrow as Arrow
import Test.Combinators as Combinators
import Test.Factum as Factum
import Test.Nomos as Nomos

main :: Effect Unit
main = do
  log "╔════════════════════════════════════════════════════════════╗"
  log "║           Noema Core Test Suite                            ║"
  log "╚════════════════════════════════════════════════════════════╝"
  log ""
  Arrow.main
  log ""
  Combinators.main
  log ""
  Factum.main
  log ""
  Nomos.main
  log ""
  log "╔════════════════════════════════════════════════════════════╗"
  log "║           Noema Core Test Suite Complete                   ║"
  log "╚════════════════════════════════════════════════════════════╝"
