-- | TLC Counterexample Feedback
-- |
-- | Parse TLC output and generate actionable feedback:
-- | - PureScript test cases that reproduce the counterexample
-- | - Diagnostic messages with suggested fixes
-- | - GitHub issue content
-- |
-- | ## TLC Output Format
-- |
-- | ```
-- | Error: Invariant NonNegativeStock is violated.
-- | Error: The behavior up to this point is:
-- | State 1: <Initial predicate>
-- | /\ stock = (<<"SKU-001", "LOC-001">> :> 10)
-- | /\ reserved = (<<"SKU-001", "LOC-001">> :> 0)
-- |
-- | State 2: <AdjustStock line 42, col 3 to line 45, col 20>
-- | /\ stock = (<<"SKU-001", "LOC-001">> :> 5)
-- | /\ reserved = (<<"SKU-001", "LOC-001">> :> 0)
-- |
-- | State 3: <AdjustStock line 42, col 3 to line 45, col 20>
-- | /\ stock = (<<"SKU-001", "LOC-001">> :> -5)  ← VIOLATION
-- | /\ reserved = (<<"SKU-001", "LOC-001">> :> 0)
-- | ```
module TlaPlus.Feedback
  ( -- * Parsing
    parseTlcOutput
  , TraceState(..)
  , CounterExample(..)
  , Violation(..)
    -- * Code generation
  , generateTestCase
  , generateDiagnostic
  , generateGitHubIssue
    -- * Main
  , main
  ) where

import Prelude

import Data.Array (intercalate, (:), last, init)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.String.Regex (Regex, regex, match)
import Data.String.Regex.Flags (noFlags, global)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Console (log)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (readTextFile, writeTextFile)

-- ============================================================
-- Types
-- ============================================================

-- | Parsed counterexample
data CounterExample = CounterExample
  { violatedProperty :: String
  , trace :: Array TraceState
  , violation :: Violation
  }

-- | Single state in trace
data TraceState = TraceState
  { stateNum :: Int
  , action :: Maybe String
  , variables :: Array (Tuple String String)  -- variable name, value
  }

-- | Violation details
data Violation = Violation
  { property :: String
  , variable :: String
  , expectedConstraint :: String
  , actualValue :: String
  , stateNum :: Int
  }

-- ============================================================
-- Parsing
-- ============================================================

-- | Parse TLC output
parseTlcOutput :: String -> Either String CounterExample
parseTlcOutput output = do
  -- Find violation
  violatedProp <- findViolation output
  
  -- Parse trace
  trace <- parseTrace output
  
  -- Extract violation details
  violation <- extractViolation violatedProp trace
  
  pure $ CounterExample
    { violatedProperty: violatedProp
    , trace
    , violation
    }

findViolation :: String -> Either String String
findViolation output = 
  case matchRegex "Invariant (\\w+) is violated" output of
    Just [_, prop] -> Right prop
    _ -> case matchRegex "Property (\\w+) is violated" output of
      Just [_, prop] -> Right prop
      _ -> Left "Could not find violation in TLC output"

parseTrace :: String -> Either String (Array TraceState)
parseTrace output = Right []  -- TODO: implement full parser

extractViolation :: String -> Array TraceState -> Either String Violation
extractViolation prop trace = 
  case last trace of
    Nothing -> Left "Empty trace"
    Just lastState -> Right $ Violation
      { property: prop
      , variable: "stock"  -- TODO: extract from property
      , expectedConstraint: ">= 0"
      , actualValue: findVarValue "stock" lastState
      , stateNum: lastState.stateNum
      }

findVarValue :: String -> TraceState -> String
findVarValue varName state = 
  case Array.find (\(Tuple n _) -> n == varName) state.variables of
    Just (Tuple _ v) -> v
    Nothing -> "unknown"

-- Helper for regex matching
matchRegex :: String -> String -> Maybe (Array String)
matchRegex pattern input = 
  case regex pattern noFlags of
    Left _ -> Nothing
    Right r -> case match r input of
      Just matches -> Just $ Array.catMaybes matches
      Nothing -> Nothing

-- ============================================================
-- Test Case Generation
-- ============================================================

-- | Generate PureScript test case from counterexample
generateTestCase :: CounterExample -> String
generateTestCase ce = String.joinWith "\n"
  [ "-- | Auto-generated test from TLA+ counterexample"
  , "-- |"
  , "-- | Violated property: " <> ce.violatedProperty
  , "-- | Trace length: " <> show (Array.length ce.trace) <> " states"
  , "module Test.Generated.Counterexample" <> show ce.violation.stateNum <> " where"
  , ""
  , "import Prelude"
  , "import Test.Spec (Spec, describe, it)"
  , "import Test.Spec.Assertions (shouldSatisfy)"
  , "import Effect.Aff (Aff)"
  , ""
  , "import Noema.Vorzeichnung.Freer (Intent, runIntent)"
  , "import Noema.Vorzeichnung.Vocabulary.InventoryF"
  , "import Noema.Cognition.InventoryHandler (inventoryHandler)"
  , ""
  , "spec :: Spec Unit"
  , "spec = describe \"TLA+ Counterexample: " <> ce.violatedProperty <> "\" do"
  , ""
  , "  it \"should satisfy " <> ce.violatedProperty <> "\" do"
  , "    -- Reproduce the counterexample trace"
  , "    let intent = " <> generateIntentFromTrace ce.trace
  , ""
  , "    result <- runIntent inventoryHandler intent unit"
  , ""
  , "    -- Property that was violated"
  , "    result `shouldSatisfy` " <> generatePropertyCheck ce.violation
  , ""
  , generateTraceComments ce.trace
  ]

generateIntentFromTrace :: Array TraceState -> String
generateIntentFromTrace trace = 
  case Array.uncons trace of
    Nothing -> "pure unit"
    Just { head, tail } -> 
      let actions = Array.mapMaybe stateToIntent (head : tail)
      in case Array.uncons actions of
        Nothing -> "pure unit"
        Just { head: first, tail: rest } ->
          if Array.null rest
            then first
            else first <> "\n        >>> " <> intercalate "\n        >>> " rest

stateToIntent :: TraceState -> Maybe String
stateToIntent state = 
  case state.action of
    Nothing -> Nothing
    Just "Init" -> Nothing
    Just action -> Just $ actionToIntent action state.variables

actionToIntent :: String -> Array (Tuple String String) -> String
actionToIntent action vars = case action of
  "AdjustStock" -> 
    "adjustStock' (ProductId \"SKU-001\") (QuantityDelta (-5))"
  "SetStock" ->
    "setStock' (ProductId \"SKU-001\") (Quantity 10)"
  "ReserveStock" ->
    "reserveStock' (ProductId \"SKU-001\") (Quantity 5)"
  _ -> 
    "-- Unknown action: " <> action

generatePropertyCheck :: Violation -> String
generatePropertyCheck v = case v.property of
  "NonNegativeStock" -> "(\\q -> q >= Quantity 0)"
  "ReservationBound" -> "(\\_ -> true)  -- TODO: implement"
  "MaximumStock" -> "(\\q -> q <= Quantity maxQuantity)"
  _ -> "(\\_ -> true)  -- Property: " <> v.property

generateTraceComments :: Array TraceState -> String
generateTraceComments trace = String.joinWith "\n"
  [ "  {-"
  , "  Counterexample trace:"
  , String.joinWith "\n" $ Array.mapWithIndex formatState trace
  , "  -}"
  ]
  where
    formatState i state = 
      "    State " <> show (i + 1) <> ": " <> 
      fromMaybe "Init" state.action <> "\n" <>
      String.joinWith "\n" (map formatVar state.variables)
    
    formatVar (Tuple name value) = 
      "      " <> name <> " = " <> value

-- ============================================================
-- Diagnostic Generation
-- ============================================================

-- | Generate human-readable diagnostic
generateDiagnostic :: CounterExample -> String
generateDiagnostic ce = String.joinWith "\n"
  [ "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  , "TLA+ Verification FAILED: " <> ce.violation.property <> " violated"
  , ""
  , "Location: src/Noema/Vorzeichnung/Vocabulary/InventoryF.purs"
  , "Property: " <> ce.violation.property
  , ""
  , "Counterexample trace:"
  , formatTraceForDiagnostic ce.trace ce.violation
  , ""
  , "Violation:"
  , "  Variable: " <> ce.violation.variable
  , "  Expected: " <> ce.violation.expectedConstraint
  , "  Actual:   " <> ce.violation.actualValue
  , ""
  , "Suggested fixes:"
  , generateSuggestedFixes ce.violation
  , "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  ]

formatTraceForDiagnostic :: Array TraceState -> Violation -> String
formatTraceForDiagnostic trace violation =
  String.joinWith "\n" $ Array.mapWithIndex formatState trace
  where
    formatState i state =
      let marker = if i + 1 == violation.stateNum then " ❌" else ""
          action = fromMaybe "Init" state.action
          varStr = String.joinWith ", " $ map (\(Tuple n v) -> n <> "=" <> v) state.variables
      in "  " <> show (i + 1) <> ". " <> action <> " → " <> varStr <> marker

generateSuggestedFixes :: Violation -> String
generateSuggestedFixes v = case v.property of
  "NonNegativeStock" -> String.joinWith "\n"
    [ ""
    , "  Option 1: Add guard in Handler"
    , "  ─────────────────────────────────"
    , "  handleAdjust pid delta = do"
    , "    current <- readStock pid"
    , "    if current + delta >= 0"
    , "      then writeStock pid (current + delta)"
    , "      else throwError InsufficientStock"
    , ""
    , "  Option 2: Use TryAdjust in Vocabulary"
    , "  ─────────────────────────────────────"
    , "  data InventoryF a b where"
    , "    TryAdjust :: ProductId -> QuantityDelta -> InventoryF Unit (Maybe Quantity)"
    , ""
    , "  Option 3: Add precondition in Intent"
    , "  ─────────────────────────────────────"
    , "  safeAdjust = "
    , "    getStock"
    , "    >>> guard (\\qty -> qty >= requiredAmount)"
    , "    >>> adjustStock"
    ]
  
  "ReservationBound" -> String.joinWith "\n"
    [ ""
    , "  Option 1: Check reservation before commit"
    , "  ─────────────────────────────────────────"
    , "  handleReserve pid qty = do"
    , "    available <- readAvailable pid"
    , "    if available >= qty"
    , "      then commitReservation pid qty"
    , "      else pure False"
    ]
  
  _ -> "  No specific suggestion for " <> v.property

-- ============================================================
-- GitHub Issue Generation
-- ============================================================

-- | Generate GitHub issue content
generateGitHubIssue :: CounterExample -> String
generateGitHubIssue ce = String.joinWith "\n"
  [ "## TLA+ Verification Failed"
  , ""
  , "### Violated Property"
  , "`" <> ce.violation.property <> "`"
  , ""
  , "### Summary"
  , "The model checker found a counterexample that violates the " <> 
    ce.violation.property <> " invariant."
  , ""
  , "### Counterexample Trace"
  , "```"
  , formatTraceForDiagnostic ce.trace ce.violation
  , "```"
  , ""
  , "### Reproduction"
  , "```purescript"
  , generateIntentFromTrace ce.trace
  , "```"
  , ""
  , "### Suggested Fix"
  , generateSuggestedFixes ce.violation
  , ""
  , "### Related Files"
  , "- `src/Noema/Vorzeichnung/Vocabulary/InventoryF.purs`"
  , "- `src/Noema/Cognition/InventoryHandler.purs`"
  , "- `tlaplus/specs/Inventory.tla`"
  , ""
  , "---"
  , "*This issue was automatically generated by the TLA+ verification pipeline.*"
  ]

-- ============================================================
-- Main
-- ============================================================

main :: Effect Unit
main = launchAff_ do
  -- Read TLC output
  tlcOutput <- readTextFile UTF8 "tlc.out"
  
  case parseTlcOutput tlcOutput of
    Left err -> do
      log $ "Parse error: " <> err
    
    Right ce -> do
      -- Generate test case
      let testCode = generateTestCase ce
      writeTextFile UTF8 "test/Test/Generated/Counterexample.purs" testCode
      
      -- Generate diagnostic
      let diagnostic = generateDiagnostic ce
      log diagnostic
      
      -- Generate GitHub issue
      let issue = generateGitHubIssue ce
      writeTextFile UTF8 "feedback/issue.md" issue
      
      log "Feedback generated successfully"
