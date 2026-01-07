---- MODULE InventorySimple ----
EXTENDS Integers, FiniteSets

CONSTANTS ProductIds, LocationIds, MaxQuantity, Channels

VARIABLES stock, reserved, pendingSync

vars == <<stock, reserved, pendingSync>>

TypeOK ==
  /\ stock \in [ProductIds \X LocationIds -> 0..MaxQuantity]
  /\ reserved \in [ProductIds \X LocationIds -> 0..MaxQuantity]
  /\ pendingSync \in [ProductIds -> SUBSET Channels]

Init ==
  /\ stock = [p \in ProductIds, l \in LocationIds |-> 0]
  /\ reserved = [p \in ProductIds, l \in LocationIds |-> 0]
  /\ pendingSync = [p \in ProductIds |-> {}]

SetStock(pid, lid, qty) ==
  /\ qty >= 0 /\ qty <= MaxQuantity
  /\ stock' = [stock EXCEPT ![<<pid, lid>>] = qty]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
  /\ UNCHANGED reserved

AdjustStock(pid, lid, delta) ==
  LET newQty == stock[<<pid, lid>>] + delta IN
    /\ newQty >= 0 /\ newQty <= MaxQuantity
    /\ stock' = [stock EXCEPT ![<<pid, lid>>] = newQty]
    /\ pendingSync' = [pendingSync EXCEPT ![pid] = Channels]
    /\ UNCHANGED reserved

\* 修正: reserved + qty が MaxQuantity を超えないことをチェック
ReserveStock(pid, lid, qty) ==
  /\ qty > 0
  /\ stock[<<pid, lid>>] >= qty
  /\ reserved[<<pid, lid>>] + qty <= MaxQuantity  \* ← 追加
  /\ stock' = [stock EXCEPT ![<<pid, lid>>] = @ - qty]
  /\ reserved' = [reserved EXCEPT ![<<pid, lid>>] = @ + qty]
  /\ UNCHANGED pendingSync

\* 修正済み: stock + qty が MaxQuantity を超えないことをチェック
ReleaseReservation(pid, lid, qty) ==
  /\ qty > 0
  /\ reserved[<<pid, lid>>] >= qty
  /\ stock[<<pid, lid>>] + qty <= MaxQuantity
  /\ stock' = [stock EXCEPT ![<<pid, lid>>] = @ + qty]
  /\ reserved' = [reserved EXCEPT ![<<pid, lid>>] = @ - qty]
  /\ UNCHANGED pendingSync

SyncToChannel(pid, channel) ==
  /\ channel \in pendingSync[pid]
  /\ pendingSync' = [pendingSync EXCEPT ![pid] = @ \ {channel}]
  /\ UNCHANGED <<stock, reserved>>

Next ==
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in 1..MaxQuantity:
       SetStock(pid, lid, qty)
  \/ \E pid \in ProductIds, lid \in LocationIds, delta \in {-1, 1}:
       AdjustStock(pid, lid, delta)
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in {1, 2}:
       ReserveStock(pid, lid, qty)
  \/ \E pid \in ProductIds, lid \in LocationIds, qty \in {1, 2}:
       ReleaseReservation(pid, lid, qty)
  \/ \E pid \in ProductIds, channel \in Channels:
       SyncToChannel(pid, channel)

Spec == Init /\ [][Next]_vars

NonNegativeStock == \A pid \in ProductIds, lid \in LocationIds: stock[<<pid, lid>>] >= 0
ReservationBound == \A pid \in ProductIds, lid \in LocationIds: reserved[<<pid, lid>>] >= 0
MaximumStock == \A pid \in ProductIds, lid \in LocationIds: stock[<<pid, lid>>] <= MaxQuantity

====
