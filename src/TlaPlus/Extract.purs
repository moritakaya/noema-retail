-- | TLA+ Extraction from Intent
-- |
-- | This module extracts TLA+ specifications from Noema Intent definitions.
-- |
-- | ## Correspondence
-- |
-- | ```
-- | Intent f a b  ←→  Action(vars, vars')
-- | f >>> g       ←→  F ∘ G (sequential composition)
-- | f *** g       ←→  F ∧ G (parallel composition)
-- | arr f         ←→  vars' = f(vars)
-- | liftEffect    ←→  Primitive Action
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import TlaPlus.Extract (extractModule)
-- | 
-- | main = do
-- |   let tlaCode = extractModule "Inventory" inventoryVocabulary intents
-- |   writeTextFile "tlaplus/specs/Inventory.tla" tlaCode
-- | ```
module TlaPlus.Extract
  ( -- * Core extraction
    extractModule
  , extractAction
  , extractIntent
    -- * TLA+ AST
  , TlaModule(..)
  , TlaAction(..)
  , TlaExpr(..)
  , TlaDecl(..)
    -- * Rendering
  , renderModule
  , renderAction
  ) where

import Prelude

import Data.Array (intercalate, (:))
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.String as String

-- ============================================================
-- TLA+ AST
-- ============================================================

-- | TLA+ Module
data TlaModule = TlaModule
  { name :: String
  , extends :: Array String
  , constants :: Array TlaDecl
  , variables :: Array TlaDecl
  , definitions :: Array TlaDecl
  , actions :: Array TlaAction
  , init :: TlaExpr
  , next :: TlaExpr
  , invariants :: Array TlaExpr
  , properties :: Array TlaExpr
  }

-- | TLA+ Declaration
data TlaDecl
  = TlaConst String String          -- name, type description
  | TlaVar String String            -- name, type
  | TlaDef String (Array String) TlaExpr  -- name, params, body

-- | TLA+ Action
data TlaAction = TlaAction
  { name :: String
  , params :: Array (Tuple String String)  -- (name, type)
  , guard :: Maybe TlaExpr
  , updates :: Array TlaUpdate
  , unchanged :: Array String
  }

-- | Variable update
data TlaUpdate = TlaUpdate
  { variable :: String
  , index :: Maybe TlaExpr      -- for function update [f EXCEPT ![i] = ...]
  , newValue :: TlaExpr
  }

-- | TLA+ Expression
data TlaExpr
  = TlaVar' String                           -- variable reference
  | TlaConst' String                         -- constant reference
  | TlaNum Int                               -- integer literal
  | TlaStr String                            -- string literal
  | TlaBool Boolean                          -- boolean literal
  | TlaApp String (Array TlaExpr)            -- function application
  | TlaBinOp String TlaExpr TlaExpr          -- binary operator
  | TlaUnOp String TlaExpr                   -- unary operator
  | TlaIf TlaExpr TlaExpr TlaExpr            -- IF ... THEN ... ELSE
  | TlaLet (Array (Tuple String TlaExpr)) TlaExpr  -- LET ... IN
  | TlaForall String TlaExpr TlaExpr         -- \A x \in S: P
  | TlaExists String TlaExpr TlaExpr         -- \E x \in S: P
  | TlaSet (Array TlaExpr)                   -- {a, b, c}
  | TlaSeq (Array TlaExpr)                   -- <<a, b, c>>
  | TlaRecord (Array (Tuple String TlaExpr)) -- [a |-> 1, b |-> 2]
  | TlaIndex TlaExpr TlaExpr                 -- f[x]
  | TlaExcept TlaExpr TlaExpr TlaExpr        -- [f EXCEPT ![x] = y]
  | TlaPrimed String                         -- var'
  | TlaUnchanged (Array String)              -- UNCHANGED <<a, b>>
  | TlaConj (Array TlaExpr)                  -- /\ ... /\ ...
  | TlaDisj (Array TlaExpr)                  -- \/ ... \/ ...
  | TlaRaw String                            -- raw TLA+ code

-- ============================================================
-- Extraction from Intent
-- ============================================================

-- | Extract TLA+ module from vocabulary and intents
extractModule 
  :: String                          -- ^ Module name
  -> Array VocabularyEntry           -- ^ Vocabulary (Functor constructors)
  -> Array IntentEntry               -- ^ Named intents
  -> TlaModule
extractModule name vocab intents = TlaModule
  { name
  , extends: ["Integers", "Sequences", "FiniteSets"]
  , constants: extractConstants vocab
  , variables: extractVariables vocab
  , definitions: []
  , actions: map extractVocabAction vocab <> map extractIntentAction intents
  , init: extractInit vocab
  , next: extractNext vocab intents
  , invariants: []
  , properties: []
  }

-- | Vocabulary entry (from InventoryF, etc.)
type VocabularyEntry =
  { constructor :: String
  , inputType :: String
  , outputType :: String
  , stateChanges :: Array StateChange
  }

-- | State change specification
type StateChange =
  { variable :: String
  , updateExpr :: String  -- TLA+ expression template
  }

-- | Named intent entry
type IntentEntry =
  { name :: String
  , intent :: IntentAst  -- Simplified Intent AST
  }

-- | Simplified Intent AST for extraction
data IntentAst
  = IntentArr String                      -- arr f (pure function)
  | IntentLift String (Array String)      -- liftEffect constructor args
  | IntentSeq IntentAst IntentAst         -- f >>> g
  | IntentPar IntentAst IntentAst         -- f *** g
  | IntentFirst IntentAst                 -- first f

-- | Extract action from vocabulary entry
extractVocabAction :: VocabularyEntry -> TlaAction
extractVocabAction entry = TlaAction
  { name: entry.constructor
  , params: inferParams entry
  , guard: inferGuard entry
  , updates: map toUpdate entry.stateChanges
  , unchanged: inferUnchanged entry
  }
  where
    inferParams _ = []  -- TODO: implement
    inferGuard _ = Nothing
    toUpdate sc = TlaUpdate
      { variable: sc.variable
      , index: Nothing
      , newValue: TlaRaw sc.updateExpr
      }
    inferUnchanged _ = []

-- | Extract action from intent
extractIntentAction :: IntentEntry -> TlaAction
extractIntentAction entry = 
  case entry.intent of
    IntentArr f ->
      TlaAction
        { name: entry.name
        , params: []
        , guard: Nothing
        , updates: []
        , unchanged: ["vars"]
        }
    
    IntentLift constructor args ->
      TlaAction
        { name: entry.name
        , params: []
        , guard: Nothing
        , updates: []  -- Delegate to vocabulary action
        , unchanged: []
        }
    
    IntentSeq first second ->
      -- Sequential composition: first THEN second
      TlaAction
        { name: entry.name
        , params: []
        , guard: Nothing
        , updates: []  -- Combined updates
        , unchanged: []
        }
    
    IntentPar left right ->
      -- Parallel composition: left AND right
      TlaAction
        { name: entry.name
        , params: []
        , guard: Nothing
        , updates: []  -- Merged updates
        , unchanged: []
        }
    
    IntentFirst inner ->
      -- first f: apply f to first component of tuple
      TlaAction
        { name: entry.name
        , params: []
        , guard: Nothing
        , updates: []
        , unchanged: []
        }

extractConstants :: Array VocabularyEntry -> Array TlaDecl
extractConstants _ = 
  [ TlaConst "ProductIds" "Set of product identifiers"
  , TlaConst "LocationIds" "Set of location identifiers"
  , TlaConst "MaxQuantity" "Maximum quantity per product"
  ]

extractVariables :: Array VocabularyEntry -> Array TlaDecl
extractVariables _ =
  [ TlaVar "stock" "[ProductIds × LocationIds -> 0..MaxQuantity]"
  , TlaVar "reserved" "[ProductIds × LocationIds -> 0..MaxQuantity]"
  ]

extractInit :: Array VocabularyEntry -> TlaExpr
extractInit _ = TlaConj
  [ TlaBinOp "=" (TlaVar' "stock") 
      (TlaRaw "[p \\in ProductIds, l \\in LocationIds |-> 0]")
  , TlaBinOp "=" (TlaVar' "reserved")
      (TlaRaw "[p \\in ProductIds, l \\in LocationIds |-> 0]")
  ]

extractNext :: Array VocabularyEntry -> Array IntentEntry -> TlaExpr
extractNext vocab intents = TlaDisj $
  map (\v -> TlaRaw $ v.constructor <> "(...)") vocab <>
  map (\i -> TlaRaw $ i.name <> "(...)") intents

-- ============================================================
-- Rendering
-- ============================================================

-- | Render TLA+ module to string
renderModule :: TlaModule -> String
renderModule mod = String.joinWith "\n"
  [ "-------------------------------- MODULE " <> mod.name <> " --------------------------------"
  , ""
  , "EXTENDS " <> intercalate ", " mod.extends
  , ""
  , "\\* Constants"
  , renderConstants mod.constants
  , ""
  , "\\* Variables"
  , renderVariables mod.variables
  , ""
  , "vars == <<" <> intercalate ", " (map varName mod.variables) <> ">>"
  , ""
  , "\\* Initial State"
  , "Init =="
  , indent 2 (renderExpr mod.init)
  , ""
  , "\\* Actions"
  , String.joinWith "\n\n" (map renderAction mod.actions)
  , ""
  , "\\* Next State"
  , "Next =="
  , indent 2 (renderExpr mod.next)
  , ""
  , "\\* Specification"
  , "Spec == Init /\\ [][Next]_vars"
  , ""
  , "================================================================================"
  ]
  where
    varName (TlaVar n _) = n
    varName _ = ""

renderConstants :: Array TlaDecl -> String
renderConstants consts = String.joinWith "\n" $
  ["CONSTANTS"] <> map renderConst consts
  where
    renderConst (TlaConst name desc) = "  " <> name <> "  \\* " <> desc
    renderConst _ = ""

renderVariables :: Array TlaDecl -> String
renderVariables vars = String.joinWith "\n" $
  ["VARIABLES"] <> map renderVar vars
  where
    renderVar (TlaVar name typ) = "  " <> name <> "  \\* " <> typ
    renderVar _ = ""

-- | Render TLA+ action
renderAction :: TlaAction -> String
renderAction action = String.joinWith "\n"
  [ action.name <> "(" <> renderParams action.params <> ") =="
  , indent 2 body
  ]
  where
    body = case action.guard of
      Nothing -> renderUpdates action.updates action.unchanged
      Just g -> "/\\ " <> renderExpr g <> "\n" <> 
                indent 2 (renderUpdates action.updates action.unchanged)
    
    renderParams ps = intercalate ", " $ map (\(Tuple n t) -> n) ps
    
    renderUpdates updates unchanged = 
      let updateLines = map renderUpdate updates
          unchangedLine = if Array.null unchanged 
                          then [] 
                          else ["/\\ UNCHANGED <<" <> intercalate ", " unchanged <> ">>"]
      in String.joinWith "\n" (updateLines <> unchangedLine)
    
    renderUpdate (TlaUpdate u) = case u.index of
      Nothing -> "/\\ " <> u.variable <> "' = " <> renderExpr u.newValue
      Just idx -> "/\\ " <> u.variable <> "' = [" <> u.variable <> 
                  " EXCEPT ![" <> renderExpr idx <> "] = " <> 
                  renderExpr u.newValue <> "]"

-- | Render TLA+ expression
renderExpr :: TlaExpr -> String
renderExpr = case _ of
  TlaVar' v -> v
  TlaConst' c -> c
  TlaNum n -> show n
  TlaStr s -> "\"" <> s <> "\""
  TlaBool true -> "TRUE"
  TlaBool false -> "FALSE"
  TlaApp f args -> f <> "(" <> intercalate ", " (map renderExpr args) <> ")"
  TlaBinOp op l r -> renderExpr l <> " " <> op <> " " <> renderExpr r
  TlaUnOp op e -> op <> " " <> renderExpr e
  TlaIf c t e -> "IF " <> renderExpr c <> " THEN " <> renderExpr t <> " ELSE " <> renderExpr e
  TlaLet binds body -> 
    "LET " <> String.joinWith "\n    " (map renderBind binds) <> 
    "\nIN " <> renderExpr body
  TlaForall v s p -> "\\A " <> v <> " \\in " <> renderExpr s <> ": " <> renderExpr p
  TlaExists v s p -> "\\E " <> v <> " \\in " <> renderExpr s <> ": " <> renderExpr p
  TlaSet elems -> "{" <> intercalate ", " (map renderExpr elems) <> "}"
  TlaSeq elems -> "<<" <> intercalate ", " (map renderExpr elems) <> ">>"
  TlaRecord fields -> "[" <> intercalate ", " (map renderField fields) <> "]"
  TlaIndex f i -> renderExpr f <> "[" <> renderExpr i <> "]"
  TlaExcept f i v -> "[" <> renderExpr f <> " EXCEPT ![" <> renderExpr i <> "] = " <> renderExpr v <> "]"
  TlaPrimed v -> v <> "'"
  TlaUnchanged vs -> "UNCHANGED <<" <> intercalate ", " vs <> ">>"
  TlaConj es -> String.joinWith "\n/\\ " (map renderExpr es)
  TlaDisj es -> String.joinWith "\n\\/ " (map renderExpr es)
  TlaRaw s -> s
  where
    renderBind (Tuple n e) = n <> " == " <> renderExpr e
    renderField (Tuple n e) = n <> " |-> " <> renderExpr e

indent :: Int -> String -> String
indent n s = 
  let spaces = String.joinWith "" (Array.replicate n " ")
  in String.joinWith "\n" $ map (spaces <> _) (String.split (String.Pattern "\n") s)
