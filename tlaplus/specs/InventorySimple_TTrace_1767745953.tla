---- MODULE InventorySimple_TTrace_1767745953 ----
EXTENDS Sequences, TLCExt, Toolbox, InventorySimple, Naturals, TLC, InventorySimple_TEConstants

_expression ==
    LET InventorySimple_TEExpression == INSTANCE InventorySimple_TEExpression
    IN InventorySimple_TEExpression!expression
----

_trace ==
    LET InventorySimple_TETrace == INSTANCE InventorySimple_TETrace
    IN InventorySimple_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        reserved = ((<<p1, l1>> :> 4))
        /\
        pendingSync = ((p1 :> {ch1}))
        /\
        stock = ((<<p1, l1>> :> 0))
    )
----

_init ==
    /\ pendingSync = _TETrace[1].pendingSync
    /\ reserved = _TETrace[1].reserved
    /\ stock = _TETrace[1].stock
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ pendingSync  = _TETrace[i].pendingSync
        /\ pendingSync' = _TETrace[j].pendingSync
        /\ reserved  = _TETrace[i].reserved
        /\ reserved' = _TETrace[j].reserved
        /\ stock  = _TETrace[i].stock
        /\ stock' = _TETrace[j].stock

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("InventorySimple_TTrace_1767745953.json", _TETrace)

=============================================================================

 Note that you can extract this module `InventorySimple_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `InventorySimple_TEExpression.tla` file takes precedence 
  over the module `InventorySimple_TEExpression` below).

---- MODULE InventorySimple_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, InventorySimple, Naturals, TLC, InventorySimple_TEConstants

expression == 
    [
        \* To hide variables of the `InventorySimple` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        pendingSync |-> pendingSync
        ,reserved |-> reserved
        ,stock |-> stock
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_pendingSyncUnchanged |-> pendingSync = pendingSync'
        
        \* Format the `pendingSync` variable as Json value.
        \* ,_pendingSyncJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(pendingSync)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_pendingSyncModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].pendingSync # _TETrace[s-1].pendingSync
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE InventorySimple_TETrace ----
\*EXTENDS IOUtils, InventorySimple, TLC, InventorySimple_TEConstants
\*
\*trace == IODeserialize("InventorySimple_TTrace_1767745953.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE InventorySimple_TETrace ----
EXTENDS InventorySimple, TLC, InventorySimple_TEConstants

trace == 
    <<
    ([reserved |-> (<<p1, l1>> :> 0),pendingSync |-> (p1 :> {}),stock |-> (<<p1, l1>> :> 0)]),
    ([reserved |-> (<<p1, l1>> :> 0),pendingSync |-> (p1 :> {ch1}),stock |-> (<<p1, l1>> :> 2)]),
    ([reserved |-> (<<p1, l1>> :> 2),pendingSync |-> (p1 :> {ch1}),stock |-> (<<p1, l1>> :> 0)]),
    ([reserved |-> (<<p1, l1>> :> 2),pendingSync |-> (p1 :> {ch1}),stock |-> (<<p1, l1>> :> 2)]),
    ([reserved |-> (<<p1, l1>> :> 4),pendingSync |-> (p1 :> {ch1}),stock |-> (<<p1, l1>> :> 0)])
    >>
----


=============================================================================

---- MODULE InventorySimple_TEConstants ----
EXTENDS InventorySimple

CONSTANTS p1, l1, ch1

=============================================================================

---- CONFIG InventorySimple_TTrace_1767745953 ----
CONSTANTS
    ProductIds = { p1 }
    LocationIds = { l1 }
    MaxQuantity = 3
    Channels = { ch1 }
    p1 = p1
    l1 = l1
    ch1 = ch1

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Jan 07 09:32:34 JST 2026