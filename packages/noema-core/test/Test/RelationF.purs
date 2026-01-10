-- | Noema RelationF Test
-- |
-- | RelationF（関係性）モジュールのテスト。
-- |
-- | ## テスト対象
-- |
-- | - RelationKind の等値性と Show
-- | - SecurityType, AgencyScope の等値性
-- | - RelationMetadata の構造
-- | - Relation レコードの構造
module Test.RelationF where

import Prelude

import Data.Foldable (and)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

import Noema.Topos.Situs (Timestamp(..), Quantity, mkSubjectId, mkThingId, mkContractId, mkRelationId, mkQuantity)
import Noema.Vorzeichnung.Vocabulary.RelationF
  ( RelationKind(..)
  , SecurityType(..)
  , AgencyScope(..)
  , ChangeType(..)
  , ConditionType(..)
  , RelationMetadata(..)
  , Relation
  , RelationInit
  , OwnershipTransfer
  )

-- ============================================================
-- RelationKind テスト
-- ============================================================

-- | RelationKind の等値性
test_relation_kind_equality :: Effect Boolean
test_relation_kind_equality = do
  pure $
    Owns == Owns &&
    Possesses == Possesses &&
    Owns /= Possesses &&
    Contains /= Guards &&
    Reserves == Reserves &&
    Intends /= Commits

-- | RelationKind の Show
test_relation_kind_show :: Effect Boolean
test_relation_kind_show = do
  let
    results =
      [ show Contains == "Contains"
      , show Guards == "Guards"
      , show Owns == "Owns"
      , show Possesses == "Possesses"
      , show Claims == "Claims"
      , show Secures == "Secures"
      , show SharedBy == "SharedBy"
      , show Reserves == "Reserves"
      , show Commits == "Commits"
      , show Intends == "Intends"
      , show Transports == "Transports"
      , show Consigns == "Consigns"
      , show ComposedOf == "ComposedOf"
      , show BundledWith == "BundledWith"
      , show Substitutes == "Substitutes"
      , show Observes == "Observes"
      , show Tracks == "Tracks"
      , show ActsFor == "ActsFor"
      , show Restricts == "Restricts"
      ]

  pure (and results)

-- ============================================================
-- SecurityType テスト
-- ============================================================

-- | SecurityType の等値性
test_security_type_equality :: Effect Boolean
test_security_type_equality = do
  pure $
    Pledge == Pledge &&
    Lien == Lien &&
    Mortgage == Mortgage &&
    SecurityInterest == SecurityInterest &&
    RetentionOfTitle == RetentionOfTitle &&
    Pledge /= Lien &&
    Mortgage /= SecurityInterest

-- ============================================================
-- AgencyScope テスト
-- ============================================================

-- | AgencyScope の等値性
test_agency_scope_equality :: Effect Boolean
test_agency_scope_equality = do
  pure $
    GeneralAgency == GeneralAgency &&
    SpecificAgency == SpecificAgency &&
    LimitedAgency == LimitedAgency &&
    GeneralAgency /= SpecificAgency &&
    SpecificAgency /= LimitedAgency

-- ============================================================
-- ChangeType テスト
-- ============================================================

-- | ChangeType の等値性
test_change_type_equality :: Effect Boolean
test_change_type_equality = do
  pure $
    PriceChanged == PriceChanged &&
    AvailabilityChanged == AvailabilityChanged &&
    PropertyChanged == PropertyChanged &&
    Discontinued == Discontinued &&
    PriceChanged /= AvailabilityChanged

-- ============================================================
-- ConditionType テスト
-- ============================================================

-- | ConditionType の等値性
test_condition_type_equality :: Effect Boolean
test_condition_type_equality = do
  let
    cid = mkContractId "contract-001"
    ts = Timestamp 1704067200000.0

    c1 = PaymentComplete cid 1000.0
    c2 = PaymentComplete cid 1000.0
    c3 = PaymentComplete cid 2000.0
    c4 = TimeElapsed ts
    c5 = ObligationFulfilled "delivery"

  pure $
    c1 == c2 &&
    c1 /= c3 &&
    c1 /= c4 &&
    c4 /= c5

-- ============================================================
-- RelationMetadata テスト
-- ============================================================

-- | SharedByMeta の構造
test_shared_by_meta :: Effect Boolean
test_shared_by_meta = do
  let
    meta = SharedByMeta { share: 0.5 }

  case meta of
    SharedByMeta r -> pure $ r.share == 0.5
    _ -> pure false

-- | ActsForMeta の構造
test_acts_for_meta :: Effect Boolean
test_acts_for_meta = do
  let
    meta = ActsForMeta { scope: GeneralAgency, disclosed: true }

  case meta of
    ActsForMeta r -> pure $ r.scope == GeneralAgency && r.disclosed == true
    _ -> pure false

-- | SecuresMeta の構造
test_secures_meta :: Effect Boolean
test_secures_meta = do
  let
    cid = mkContractId "contract-001"
    meta = SecuresMeta
      { securityType: Pledge
      , priority: 1
      , amount: Just 100000.0
      , securedContract: Just cid
      , ariseFrom: Nothing
      }

  case meta of
    SecuresMeta r ->
      pure $
        r.securityType == Pledge &&
        r.priority == 1 &&
        r.amount == Just 100000.0 &&
        r.securedContract == Just cid &&
        r.ariseFrom == Nothing
    _ -> pure false

-- | ExpirationMeta の構造
test_expiration_meta :: Effect Boolean
test_expiration_meta = do
  let
    ts = Timestamp 1704067200000.0
    meta = ExpirationMeta { expiresAt: ts }

  case meta of
    ExpirationMeta r -> pure $ r.expiresAt == ts
    _ -> pure false

-- | IntendsMeta の構造
test_intends_meta :: Effect Boolean
test_intends_meta = do
  let
    meta = IntendsMeta { quantity: mkQuantity 5, notifyOn: [PriceChanged, AvailabilityChanged] }

  case meta of
    IntendsMeta r -> pure $ r.quantity == mkQuantity 5 && r.notifyOn == [PriceChanged, AvailabilityChanged]
    _ -> pure false

-- ============================================================
-- Relation レコードテスト
-- ============================================================

-- | Relation の構造
test_relation_structure :: Effect Boolean
test_relation_structure = do
  let
    rid = mkRelationId "rel-001"
    sid = mkSubjectId "subject-001"
    tid = mkThingId "thing-001"
    cid = mkContractId "contract-001"
    ts = Timestamp 1704067200000.0

    relation :: Relation
    relation =
      { id: rid
      , kind: Owns
      , from: sid
      , to: tid
      , metadata: Nothing
      , validFrom: ts
      , validUntil: Nothing
      , contractRef: Just cid
      , createdAt: ts
      }

  -- Note: metadata 比較は Eq インスタンスがないためスキップ
  case relation.metadata of
    Nothing ->
      pure $
        relation.id == rid &&
        relation.kind == Owns &&
        relation.from == sid &&
        relation.to == tid &&
        relation.validFrom == ts &&
        relation.validUntil == Nothing &&
        relation.contractRef == Just cid
    Just _ -> pure false

-- | Relation with metadata
test_relation_with_metadata :: Effect Boolean
test_relation_with_metadata = do
  let
    rid = mkRelationId "rel-002"
    sid = mkSubjectId "subject-001"
    tid = mkThingId "thing-001"
    ts = Timestamp 1704067200000.0
    meta = SharedByMeta { share: 0.333 }

    relation :: Relation
    relation =
      { id: rid
      , kind: SharedBy
      , from: sid
      , to: tid
      , metadata: Just meta
      , validFrom: ts
      , validUntil: Nothing
      , contractRef: Nothing
      , createdAt: ts
      }

  case relation.metadata of
    Just (SharedByMeta r) -> pure $ r.share == 0.333
    _ -> pure false

-- ============================================================
-- RelationInit テスト
-- ============================================================

-- | RelationInit の構造
test_relation_init_structure :: Effect Boolean
test_relation_init_structure = do
  let
    sid = mkSubjectId "subject-001"
    tid = mkThingId "thing-001"
    ts = Timestamp 1735689600000.0

    init :: RelationInit
    init =
      { kind: Reserves
      , from: sid
      , to: tid
      , metadata: Just (ExpirationMeta { expiresAt: ts })
      , validUntil: Just ts
      , contractRef: Nothing
      }

  pure $
    init.kind == Reserves &&
    init.from == sid &&
    init.to == tid &&
    init.validUntil == Just ts

-- ============================================================
-- OwnershipTransfer テスト
-- ============================================================

-- | OwnershipTransfer の構造
test_ownership_transfer :: Effect Boolean
test_ownership_transfer = do
  let
    tid = mkThingId "thing-001"
    fromSid = mkSubjectId "seller-001"
    toSid = mkSubjectId "buyer-001"
    viaSid = mkSubjectId "agent-001"
    cid = mkContractId "contract-001"
    ts = Timestamp 1704067200000.0

    transfer :: OwnershipTransfer
    transfer =
      { thing: tid
      , from: fromSid
      , to: toSid
      , via: Just viaSid
      , contractRef: cid
      , timestamp: ts
      }

  pure $
    transfer.thing == tid &&
    transfer.from == fromSid &&
    transfer.to == toSid &&
    transfer.via == Just viaSid &&
    transfer.contractRef == cid

-- | OwnershipTransfer without via
test_ownership_transfer_direct :: Effect Boolean
test_ownership_transfer_direct = do
  let
    transfer :: OwnershipTransfer
    transfer =
      { thing: mkThingId "thing-002"
      , from: mkSubjectId "seller-002"
      , to: mkSubjectId "buyer-002"
      , via: Nothing
      , contractRef: mkContractId "contract-002"
      , timestamp: Timestamp 1704067200000.0
      }

  pure $ transfer.via == Nothing

-- ============================================================
-- テスト実行
-- ============================================================

-- | 全テストを実行
main :: Effect Unit
main = do
  log "=== Noema RelationF Test ==="
  log ""

  log "--- RelationKind ---"

  log "RelationKind equality"
  r1 <- test_relation_kind_equality
  log $ "  Result: " <> if r1 then "✓ PASS" else "✗ FAIL"

  log "RelationKind show"
  r2 <- test_relation_kind_show
  log $ "  Result: " <> if r2 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- SecurityType ---"

  log "SecurityType equality"
  r3 <- test_security_type_equality
  log $ "  Result: " <> if r3 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- AgencyScope ---"

  log "AgencyScope equality"
  r4 <- test_agency_scope_equality
  log $ "  Result: " <> if r4 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ChangeType ---"

  log "ChangeType equality"
  r5 <- test_change_type_equality
  log $ "  Result: " <> if r5 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- ConditionType ---"

  log "ConditionType equality"
  r6 <- test_condition_type_equality
  log $ "  Result: " <> if r6 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- RelationMetadata ---"

  log "SharedByMeta"
  r7 <- test_shared_by_meta
  log $ "  Result: " <> if r7 then "✓ PASS" else "✗ FAIL"

  log "ActsForMeta"
  r8 <- test_acts_for_meta
  log $ "  Result: " <> if r8 then "✓ PASS" else "✗ FAIL"

  log "SecuresMeta"
  r9 <- test_secures_meta
  log $ "  Result: " <> if r9 then "✓ PASS" else "✗ FAIL"

  log "ExpirationMeta"
  r10 <- test_expiration_meta
  log $ "  Result: " <> if r10 then "✓ PASS" else "✗ FAIL"

  log "IntendsMeta"
  r11 <- test_intends_meta
  log $ "  Result: " <> if r11 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- Relation ---"

  log "Relation structure"
  r12 <- test_relation_structure
  log $ "  Result: " <> if r12 then "✓ PASS" else "✗ FAIL"

  log "Relation with metadata"
  r13 <- test_relation_with_metadata
  log $ "  Result: " <> if r13 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- RelationInit ---"

  log "RelationInit structure"
  r14 <- test_relation_init_structure
  log $ "  Result: " <> if r14 then "✓ PASS" else "✗ FAIL"

  log ""
  log "--- OwnershipTransfer ---"

  log "OwnershipTransfer structure"
  r15 <- test_ownership_transfer
  log $ "  Result: " <> if r15 then "✓ PASS" else "✗ FAIL"

  log "OwnershipTransfer direct"
  r16 <- test_ownership_transfer_direct
  log $ "  Result: " <> if r16 then "✓ PASS" else "✗ FAIL"

  log ""
  let allPassed = and [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16]
  log $ "=== " <> (if allPassed then "ALL TESTS PASSED ✓" else "SOME TESTS FAILED ✗") <> " ==="
