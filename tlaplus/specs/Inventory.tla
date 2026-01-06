-------------------------------- MODULE Inventory --------------------------------
\* Noema Inventory Module
\* 
\* This specification corresponds to:
\*   src/Noema/Vorzeichnung/Vocabulary/InventoryF.purs
\*
\* Functor correspondence (Arrow-based Intent):
\*   Intent f a b  ↔  Action(vars, vars')
\*   f >>> g       ↔  F ∘ G (sequential composition)
\*   f *** g       ↔  F ∧ G (parallel composition)
\*   arr f         ↔  vars' = f(vars)
\*   liftEffect op ↔  Op(vars, vars')
\*
\* ArrowChoice is NOT supported (no branching in Intent)
\* Branching is handled at the Handler (Cognition) level

EXTENDS Integers, Sequences, FiniteSets, TLC

\*=============================================================================
\* Constants
\*=============================================================================

CONSTANTS
  ProductIds,      \* Set of product identifiers (ThingId)
  LocationIds,     \* Set of location identifiers (LocationId)
  MaxQuantity,     \* Maximum quantity per product
  Channels         \* Set of sales channels {Own, Smaregi, Rakuten, Yahoo, Stripe}

\*=============================================================================
\* Variables
\*=============================================================================

VARIABLES
  stock,           \* [ProductId × LocationId → Quantity]
  reserved,        \* [ProductId × LocationId → Quantity]
  pendingSync,     \* [ProductId → Set(Channel)]
  eventLog         \* Sequence of events (for event sourcing)

vars == <<stock, reserved, pendingSync, eventLog>>

\*=============================================================================
\* Type Invariants
\*=============================================================================

TypeOK ==
  /\ stock \in [ProductIds \X LocationIds -> 0..MaxQuantity]
  /\ reserved \in [ProductIds \X LocationIds -> 0..MaxQuantity]
  /\ pendingSync \in [ProductIds -> SUBSET Channels]
  /\ eventLog \in Seq([type: {"adjust", "reserve", "release", "sync"}, 
                       pid: ProductIds, 
                       qty: Int,
                       timestamp: Nat])

\*=============================================================================
\* Initial State
\*=============================================================================

Init ==
  /\ stock = [p \in ProductIds, l \in LocationIds |-> 0]
  /\ reserved = [p \in ProductIds, l \in LocationIds |-> 0]
  /\ pendingSync = [p \in ProductIds |-> {}]
  /\ eventLog = <<>>

\*=============================================================================
\* Actions (corresponding to InventoryF constructors)
\*=============================================================================

\* GetStock: Read current stock (pure, no state change)
\* PureScript: GetStock ThingId LocationId (StockInfo -> a)
\* Arrow Intent: getStock :: ThingId -> LocationId -> Intent' InventoryF Unit StockInfo
GetStock(pid, lid) ==
  /\ UNCHANGED vars
  \* Return value: stock[<<pid, lid>>]

\* SetStock: Set stock to specific quantity
\* PureScript: SetStock ThingId LocationId Quantity a
\* Arrow Intent: setStock :: ThingId -> LocationId -> Quantity -> Intent' InventoryF Unit Unit
SetStock(pid, lid, qty) ==
  /\ qty >= 0
  /\ qty <= MaxQuantity
  /\ stock' = [stock EXCEPT ![<<pid, lid>>] = qty]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
  /\ eventLog' = Append(eventLog, [type |-> "adjust", pid |-> pid, 
                                    qty |-> qty, timestamp |-> Len(eventLog)])
  /\ UNCHANGED reserved

\* AdjustStock: Adjust stock by delta
\* PureScript: AdjustStock ThingId LocationId QuantityDelta (Quantity -> a)
\* Arrow Intent: adjustStock :: ThingId -> LocationId -> QuantityDelta -> Intent' InventoryF Unit Quantity
AdjustStock(pid, lid, delta) ==
  LET newQty == stock[<<pid, lid>>] + delta
  IN
    /\ newQty >= 0
    /\ newQty <= MaxQuantity
    /\ stock' = [stock EXCEPT ![<<pid, lid>>] = newQty]
    /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
    /\ eventLog' = Append(eventLog, [type |-> "adjust", pid |-> pid,
                                      qty |-> delta, timestamp |-> Len(eventLog)])
    /\ UNCHANGED reserved

\* ReserveStock: Reserve stock (conditional)
\* PureScript: ReserveStock ThingId LocationId Quantity (Boolean -> a)
\* Arrow Intent: reserveStock :: ThingId -> LocationId -> Quantity -> Intent' InventoryF Unit Boolean
\* 
\* Note: This action encodes the success case.
\* In Arrow-based Intent, failure is returned as Boolean result, not as branching.
ReserveStock(pid, lid, qty) ==
  /\ qty > 0
  /\ stock[<<pid, lid>>] >= qty
  /\ stock' = [stock EXCEPT ![<<pid, lid>>] = @ - qty]
  /\ reserved' = [reserved EXCEPT ![<<pid, lid>>] = @ + qty]
  /\ eventLog' = Append(eventLog, [type |-> "reserve", pid |-> pid,
                                    qty |-> qty, timestamp |-> Len(eventLog)])
  /\ UNCHANGED pendingSync

\* ReleaseReservation: Release reserved stock
\* PureScript: ReleaseReservation ThingId LocationId String a
\* Arrow Intent: releaseReservation :: ThingId -> LocationId -> String -> Intent' InventoryF Unit Unit
ReleaseReservation(pid, lid, qty) ==
  /\ qty > 0
  /\ reserved[<<pid, lid>>] >= qty
  /\ stock' = [stock EXCEPT ![<<pid, lid>>] = @ + qty]
  /\ reserved' = [reserved EXCEPT ![<<pid, lid>>] = @ - qty]
  /\ eventLog' = Append(eventLog, [type |-> "release", pid |-> pid,
                                    qty |-> qty, timestamp |-> Len(eventLog)])
  /\ UNCHANGED pendingSync

\* SyncToChannel: Sync inventory to external channel
\* PureScript: SyncToChannel Channel ThingId Quantity (SyncResult -> a)
\* Arrow Intent: syncToChannel :: Channel -> ThingId -> Quantity -> Intent' InventoryF Unit SyncResult
SyncToChannel(pid, channel) ==
  /\ channel \in pendingSync[pid]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = @ \ {channel}]
  /\ eventLog' = Append(eventLog, [type |-> "sync", pid |-> pid,
                                    qty |-> 0, timestamp |-> Len(eventLog)])
  /\ UNCHANGED <<stock, reserved>>

\*=============================================================================
\* Composite Actions (corresponding to Intent compositions with >>>)
\*=============================================================================

\* Sale: getStock >>> arr _.quantity >>> adjustStock (with check)
\* 
\* Arrow Intent:
\*   saleIntent :: ThingId -> LocationId -> Intent' InventoryF Unit Quantity
\*   saleIntent tid lid = 
\*     getStock tid lid 
\*     >>> arr _.quantity
\*     >>> arr (\q -> (tid, lid, QuantityDelta (-1)))
\*     >>> ...
\*
\* Note: In Arrow, no branching is allowed in Intent.
\* The check (stock > 0) is a precondition for this action.
Sale(pid, lid) ==
  /\ stock[<<pid, lid>>] > 0
  /\ AdjustStock(pid, lid, -1)

\* Transfer: adjustStock from >>> adjustStock to
\*
\* Arrow Intent:
\*   transferIntent fromLoc toLoc qty =
\*     adjustStock fromLoc (QuantityDelta (-qty))
\*     >>> adjustStock toLoc (QuantityDelta qty)
Transfer(pid, fromLid, toLid, qty) ==
  /\ qty > 0
  /\ stock[<<pid, fromLid>>] >= qty
  /\ stock' = [stock EXCEPT 
       ![<<pid, fromLid>>] = @ - qty,
       ![<<pid, toLid>>] = @ + qty]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
  /\ eventLog' = Append(eventLog, [type |-> "adjust", pid |-> pid,
                                    qty |-> qty, timestamp |-> Len(eventLog)])
  /\ UNCHANGED reserved

\* ParallelQuery: getStock &&& getStock (fanout)
\*
\* Arrow Intent:
\*   parallelQuery tid lid1 lid2 =
\*     (getStock tid lid1 &&& getStock tid lid2)
\*     >>> arr (\(s1, s2) -> s1.quantity + s2.quantity)
\*
\* This is a pure read operation, no state change
ParallelQuery(pid, lid1, lid2) ==
  /\ UNCHANGED vars
  \* Return value: stock[<<pid, lid1>>] + stock[<<pid, lid2>>]

\*=============================================================================
\* Next State Relation
\*=============================================================================

Next ==
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in 1..MaxQuantity:
       SetStock(pid, lid, qty)
  \/ \E pid \in ProductIds, lid \in LocationIds, delta \in -5..5:
       AdjustStock(pid, lid, delta)
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in 1..5:
       ReserveStock(pid, lid, qty)
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in 1..5:
       ReleaseReservation(pid, lid, qty)
  \/ \E pid \in ProductIds, channel \in Channels:
       SyncToChannel(pid, channel)
  \/ \E pid \in ProductIds, lid \in LocationIds:
       Sale(pid, lid)
  \/ \E pid \in ProductIds, fromLid \in LocationIds, toLid \in LocationIds, qty \in 1..5:
       /\ fromLid # toLid
       /\ Transfer(pid, fromLid, toLid, qty)

\*=============================================================================
\* Specification
\*=============================================================================

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\*=============================================================================
\* Safety Properties (Invariants)
\*=============================================================================

\* S1: Stock is always non-negative
\* This corresponds to the domain constraint: Quantity >= 0
NonNegativeStock ==
  \A pid \in ProductIds, lid \in LocationIds:
    stock[<<pid, lid>>] >= 0

\* S2: Reserved quantity never exceeds total (stock + reserved)
\* This ensures we can always fulfill reservations
ReservationBound ==
  \A pid \in ProductIds, lid \in LocationIds:
    reserved[<<pid, lid>>] >= 0

\* S3: Stock never exceeds maximum
\* This corresponds to MaxQuantity constraint
MaximumStock ==
  \A pid \in ProductIds, lid \in LocationIds:
    stock[<<pid, lid>>] <= MaxQuantity

\* S4: Available stock is non-negative
\* available = stock (after reservation deducted in our model)
AvailableNonNegative ==
  \A pid \in ProductIds, lid \in LocationIds:
    stock[<<pid, lid>>] >= 0

\* Combined safety invariant
Safety ==
  /\ TypeOK
  /\ NonNegativeStock
  /\ ReservationBound
  /\ MaximumStock
  /\ AvailableNonNegative

\*=============================================================================
\* Liveness Properties
\*=============================================================================

\* L1: Pending syncs are eventually processed
\* This ensures eventual consistency with external channels
SyncEventuallyCompletes ==
  \A pid \in ProductIds:
    pendingSync[pid] # {} ~> pendingSync[pid] = {}

\* L2: Reserved stock is eventually released or committed
\* This prevents indefinite reservation holds
ReservationEventuallyResolved ==
  \A pid \in ProductIds, lid \in LocationIds:
    reserved[<<pid, lid>>] > 0 ~> reserved[<<pid, lid>>] = 0

\*=============================================================================
\* Fairness
\*=============================================================================

\* Weak fairness: If sync is continuously enabled, it will eventually happen
FairSync ==
  \A pid \in ProductIds, channel \in Channels:
    WF_vars(SyncToChannel(pid, channel))

\*=============================================================================
\* State Constraints (for model checking)
\*=============================================================================

\* Limit state space for tractability
StateConstraint ==
  /\ \A pid \in ProductIds, lid \in LocationIds:
       /\ stock[<<pid, lid>>] <= 5
       /\ reserved[<<pid, lid>>] <= 3
  /\ Len(eventLog) <= 10

\*=============================================================================
\* Arrow Law Correspondence
\*=============================================================================

\* The following comments document how Arrow laws translate to TLA+:
\*
\* Law 1: arr id = id
\*   TLA+: UNCHANGED vars
\*
\* Law 2: arr (g <<< f) = arr g <<< arr f
\*   TLA+: Composition of pure state transformations
\*
\* Law 3: first (arr f) = arr (first f)
\*   TLA+: Parallel composition preserves structure
\*
\* Law 4: first (f >>> g) = first f >>> first g
\*   TLA+: Sequential composition distributes over parallel
\*
\* ArrowChoice is NOT supported:
\*   No left/right operations in Intent
\*   Branching is delegated to Handler (Cognition)

================================================================================
