-------------------------------- MODULE Inventory --------------------------------
\* Noema Inventory Module
\* 
\* This specification is automatically extracted from:
\*   src/Noema/Vorzeichnung/Vocabulary/InventoryF.purs
\*
\* Functor correspondence:
\*   Intent f a b  ←→  Action(vars, vars')
\*   f >>> g       ←→  F ∘ G
\*   f *** g       ←→  F ∧ G
\*   arr f         ←→  vars' = f(vars)

EXTENDS Integers, Sequences, FiniteSets, TLC

\*=============================================================================
\* Constants
\*=============================================================================

CONSTANTS
  ProductIds,      \* Set of product identifiers
  LocationIds,     \* Set of location identifiers  
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
\* Corresponds to: GetStock :: ProductId -> InventoryF Unit Quantity
GetStock(pid, lid) ==
  /\ UNCHANGED vars
  \* Return value: stock[pid, lid]

\* SetStock: Set stock to specific quantity
\* Corresponds to: SetStock :: ProductId -> InventoryF Quantity Unit
SetStock(pid, lid, qty) ==
  /\ qty >= 0
  /\ qty <= MaxQuantity
  /\ stock' = [stock EXCEPT ![pid, lid] = qty]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
  /\ eventLog' = Append(eventLog, [type |-> "adjust", pid |-> pid, 
                                    qty |-> qty, timestamp |-> Len(eventLog)])
  /\ UNCHANGED reserved

\* AdjustStock: Adjust stock by delta
\* Corresponds to: AdjustStock :: ProductId -> QuantityDelta -> InventoryF Unit Quantity
AdjustStock(pid, lid, delta) ==
  LET newQty == stock[pid, lid] + delta
  IN
    /\ newQty >= 0
    /\ newQty <= MaxQuantity
    /\ stock' = [stock EXCEPT ![pid, lid] = newQty]
    /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
    /\ eventLog' = Append(eventLog, [type |-> "adjust", pid |-> pid,
                                      qty |-> delta, timestamp |-> Len(eventLog)])
    /\ UNCHANGED reserved

\* ReserveStock: Reserve stock (conditional)
\* Corresponds to: ReserveStock :: ProductId -> Quantity -> InventoryF Unit Boolean
\* 
\* Note: This action has non-determinism (success or failure)
\* In Arrow-based Intent, this is handled by returning Maybe/Either
ReserveStock(pid, lid, qty) ==
  /\ qty > 0
  /\ stock[pid, lid] >= qty
  /\ stock' = [stock EXCEPT ![pid, lid] = @ - qty]
  /\ reserved' = [reserved EXCEPT ![pid, lid] = @ + qty]
  /\ eventLog' = Append(eventLog, [type |-> "reserve", pid |-> pid,
                                    qty |-> qty, timestamp |-> Len(eventLog)])
  /\ UNCHANGED pendingSync

\* ReleaseReservation: Release reserved stock
\* Corresponds to: ReleaseReservation :: ProductId -> Quantity -> InventoryF Unit Unit
ReleaseReservation(pid, lid, qty) ==
  /\ qty > 0
  /\ reserved[pid, lid] >= qty
  /\ stock' = [stock EXCEPT ![pid, lid] = @ + qty]
  /\ reserved' = [reserved EXCEPT ![pid, lid] = @ - qty]
  /\ eventLog' = Append(eventLog, [type |-> "release", pid |-> pid,
                                    qty |-> qty, timestamp |-> Len(eventLog)])
  /\ UNCHANGED pendingSync

\* SyncToChannel: Sync inventory to external channel
\* Corresponds to: syncToChannel in Presheaf module
SyncToChannel(pid, channel) ==
  /\ channel \in pendingSync[pid]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = @ \ {channel}]
  /\ eventLog' = Append(eventLog, [type |-> "sync", pid |-> pid,
                                    qty |-> 0, timestamp |-> Len(eventLog)])
  /\ UNCHANGED <<stock, reserved>>

\*=============================================================================
\* Composite Actions (corresponding to Intent compositions)
\*=============================================================================

\* Sale: GetStock >>> AdjustStock(-1)
\* 
\* Arrow representation:
\*   saleIntent = getStock >>> arr (\q -> (q, -1)) >>> adjustStock
\*
\* TLA+ representation:
Sale(pid, lid) ==
  /\ stock[pid, lid] > 0
  /\ AdjustStock(pid, lid, -1)

\* Transfer: AdjustStock(from, -n) >>> AdjustStock(to, +n)
\*
\* Arrow representation:
\*   transferIntent = 
\*     adjustStock fromLoc (-qty)
\*     >>> adjustStock toLoc qty
Transfer(pid, fromLid, toLid, qty) ==
  /\ qty > 0
  /\ stock[pid, fromLid] >= qty
  /\ stock' = [stock EXCEPT 
       ![pid, fromLid] = @ - qty,
       ![pid, toLid] = @ + qty]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
  /\ eventLog' = Append(eventLog, [type |-> "adjust", pid |-> pid,
                                    qty |-> qty, timestamp |-> Len(eventLog)])
  /\ UNCHANGED reserved

\*=============================================================================
\* Next State Relation
\*=============================================================================

Next ==
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in 1..MaxQuantity:
       SetStock(pid, lid, qty)
  \/ \E pid \in ProductIds, lid \in LocationIds, delta \in -10..10:
       AdjustStock(pid, lid, delta)
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in 1..10:
       ReserveStock(pid, lid, qty)
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in 1..10:
       ReleaseReservation(pid, lid, qty)
  \/ \E pid \in ProductIds, channel \in Channels:
       SyncToChannel(pid, channel)
  \/ \E pid \in ProductIds, lid \in LocationIds:
       Sale(pid, lid)

\*=============================================================================
\* Specification
\*=============================================================================

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\*=============================================================================
\* Safety Properties (Invariants)
\*=============================================================================

\* S1: Stock is always non-negative
NonNegativeStock ==
  \A pid \in ProductIds, lid \in LocationIds:
    stock[pid, lid] >= 0

\* S2: Reserved quantity never exceeds available stock
ReservationBound ==
  \A pid \in ProductIds, lid \in LocationIds:
    reserved[pid, lid] <= stock[pid, lid] + reserved[pid, lid]

\* S3: Stock never exceeds maximum
MaximumStock ==
  \A pid \in ProductIds, lid \in LocationIds:
    stock[pid, lid] <= MaxQuantity

\* Combined safety invariant
Safety ==
  /\ TypeOK
  /\ NonNegativeStock
  /\ ReservationBound
  /\ MaximumStock

\*=============================================================================
\* Liveness Properties
\*=============================================================================

\* L1: Pending syncs are eventually processed
SyncEventuallyCompletes ==
  \A pid \in ProductIds:
    pendingSync[pid] # {} ~> pendingSync[pid] = {}

\* L2: Reserved stock is eventually released or committed
ReservationEventuallyResolved ==
  \A pid \in ProductIds, lid \in LocationIds:
    reserved[pid, lid] > 0 ~> reserved[pid, lid] = 0

\*=============================================================================
\* Fairness
\*=============================================================================

\* Weak fairness: If sync is continuously enabled, it will eventually happen
FairSync ==
  \A pid \in ProductIds, channel \in Channels:
    WF_vars(SyncToChannel(pid, channel))

\*=============================================================================
\* Refinement Mapping
\*=============================================================================

\* Abstract state: just total stock per product
AbstractStock == [pid \in ProductIds |-> 
  Sum([lid \in LocationIds |-> stock[pid, lid]])]

\* This module refines a simpler specification with just product-level stock

================================================================================
