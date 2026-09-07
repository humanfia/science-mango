import Family8Grounding.Family8ParentwiseBadParentMassAwareFactorListStateV2
import Family8Grounding.Family8ParentwiseBadParentMassAwareActiveCoarseConnectorV1
import Mathlib.Tactic

/-!
# Dual-child orchestration certificate for a parentwise bad factor

One bad-parent step produces two genuinely different recursive objects.

* The `q`-fibre child is selected inside one literal parent and has actual
  radius `badParentFreshChildRadius delta rho = (3/64) * (delta/rho)`.
* The active-parent child is selected from all active coarse occurrences and
  has actual radius `rho/8`.

This certificate keeps the two selections, admissibility proofs, analytic
obligations, and mass losses in separate fields.  Only the `q`-fibre child
participates in the existing `3/64` factor-list product identity.  No callback
or identification of the two children is stored.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentDualChildOrchestrationCertificateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8ParentwiseBadParentMassAwareActiveCoarseConnectorV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8StickyActiveCoarseAdmissibleChildV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- Formal orchestration state with two separately typed child certificates.
The `activeParentState` retains the conflict/KT assumptions as fields, while
the `qFibreState` retains the same-selected proxy Frostman and factor-product
certificates. -/
structure ParentwiseBadParentDualChildCertificate
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (lower factorC : ENNReal)
    (conflictThreshold : Nat) (activeC : ENNReal) where
  qFibreState : ParentwiseBadParentMassAwareFactorListState
    D S left right hrho hrhoOne q lower factorC
  activeParentState : ActiveCoarseAdmissibleFactorState
    D S conflictThreshold activeC

namespace ParentwiseBadParentDualChildCertificate

variable {D : ActualTubeDatum delta iota}
  {S : StickyScaleCover D.family rho}
  {left right : List ActualFactorDatum}
  {hrho : 0 < rho} {hrhoOne : rho <= 1}
  {q : {q // q ∈ S.activeCoarse}}
  {lower factorC activeC : ENNReal} {conflictThreshold : Nat}

/-- The selected subtype inside the one fixed bad parent `q`. -/
def qFibreSelected
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    Finset {i // i ∈ S.fiber q.1} :=
  X.qFibreState.base.selected

/-- The independently selected subtype of all active coarse occurrences. -/
def activeParentSelected
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    Finset {k // k ∈ S.activeCoarse} :=
  X.activeParentState.selected

/-- The literal same-`q` contracted-John fresh child. -/
def qFibreChildDatum
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :=
  badParentFreshSuccessorDatum
    S D.shading hrho hrhoOne q X.qFibreSelected

/-- The independent eighth-normalized fresh child of active parents. -/
def activeParentChildDatum
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :=
  activeCoarseFreshChildDatum D S X.activeParentSelected

/-- Package the same-`q` child without changing its literal actual radius. -/
def qFibreChildAtom
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) : ActualFactorDatum :=
  ActualFactorDatum.ofDatum X.qFibreChildDatum

/-- Package the active-parent child without changing its literal actual
radius.  It is a next-step object, not an extra atom silently inserted into
the existing `3/64` successor list. -/
def activeParentChildAtom
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) : ActualFactorDatum :=
  ActualFactorDatum.ofDatum X.activeParentChildDatum

@[simp] theorem qFibreChildAtom_radius
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    X.qFibreChildAtom.radius = badParentFreshChildRadius delta rho :=
  rfl

@[simp] theorem activeParentChildAtom_radius
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    X.activeParentChildAtom.radius = rho / 8 :=
  rfl

/-- The exact `q`-fibre coefficient remains explicit. -/
theorem qFibreChild_radius_eq_fixed_mul_ratio
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    X.qFibreChildAtom.radius =
      (3 / 64 : NNReal) * (delta / rho) := by
  rw [qFibreChildAtom_radius]
  exact badParentFreshChildRadius_eq_fixed_mul_ratio hrho

theorem qFibreChild_admissible
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    X.qFibreChildDatum.IsAdmissible := by
  exact X.qFibreState.base.child_admissible

theorem activeParentChild_admissible
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    X.activeParentChildDatum.IsAdmissible := by
  exact X.activeParentState.child_admissible

/-- The same-`q` child's mass retention has its own geometric/fibre loss. -/
theorem qFibre_shadingMass_loss
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    (badParentRescaledFibreDatum
      S D.shading hrho hrhoOne q).shading.shadingMass <=
      badParentFreshRetentionLoss
          S hrho hrhoOne q X.qFibreSelected lower *
        X.qFibreChildDatum.shading.shadingMass := by
  exact X.qFibreState.base.shading_mass_retention

/-- The active-parent child's normalized mass loss is a different field and
depends only on the explicit conflict threshold. -/
theorem activeParent_normalizedShadingMass_loss
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    (eighthNormalizedDatum
      (activeCoarseAggregatedDatum D S)).shading.shadingMass <=
        (conflictThreshold + 1 : Nat) *
          X.activeParentChildDatum.shading.shadingMass := by
  exact X.activeParentState.normalized_mass_loss

/-- The active-parent conflict obligation remains inspectable in the formal
orchestration state. -/
theorem activeParent_conflict_cap
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    forall a : {k // k ∈ S.activeCoarse},
      (normalizedConflictIndices
        (activeCoarseAggregatedDatum D S) a).card <= conflictThreshold :=
  X.activeParentState.conflict_cap

/-- The active-parent KT obligation remains inspectable independently of the
factor's fibre-cardinality uniformity constant. -/
theorem activeParent_katzTao_at_scale
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    S.IsKatzTaoAtScale activeC :=
  X.activeParentState.katzTao_at_scale

/-- Only the same-`q` factor-list replacement carries the fixed `3/64`
surrounding-list product identity. -/
theorem qFibre_successor_radiusProduct
    (X : ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) :
    factorRadiusProduct X.qFibreState.successorFactors =
      (3 / 64 : NNReal) *
        factorRadiusProduct X.qFibreState.sourceFactors :=
  X.qFibreState.successor_radiusProduct

end ParentwiseBadParentDualChildCertificate

/-! ## Callback-free orchestration producer -/

/-- Build both positive successor certificates.  The existing bad-parent
inputs construct the same-`q` state; the two additional explicit analytic
obligations construct the independent active-parent state. -/
theorem exists_parentwiseBadParentDualChildCertificate
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hrhoSixteenth : rho <= (1 / 16 : NNReal))
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse})
    (lower factorC : ENNReal) (hlowerTop : lower ≠ ∞)
    (hbad : parentNormalizedFiberCFAt S q < lower)
    (huniform : IsCUniform S factorC)
    (conflictThreshold : Nat)
    (hconflict : forall a : {k // k ∈ S.activeCoarse},
      (normalizedConflictIndices
        (activeCoarseAggregatedDatum D S) a).card <= conflictThreshold)
    (activeC : ENNReal) (hKT : S.IsKatzTaoAtScale activeC) :
    Nonempty (ParentwiseBadParentDualChildCertificate
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) := by
  have hrhoHalf : rho <= (2 : NNReal)⁻¹ := by
    have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
      change (1 : Real) / 16 <= (2 : Real)⁻¹
      norm_num
    exact hrhoSixteenth.trans hsixteenHalf
  obtain ⟨qFibreState⟩ :=
    exists_parentwiseBadParentMassAwareFactorListState
      D S left right hD.delta_pos hD.delta_le_half hrho hrhoOne
        hdeltaRho q hlowerTop hbad huniform
  obtain ⟨activeParentState⟩ :=
    exists_activeCoarseAdmissibleFactorState
      D hD S hrho hrhoHalf hrhoSixteenth ⟨q.1, q.2⟩
        conflictThreshold hconflict activeC hKT
  exact ⟨
    { qFibreState := qFibreState
      activeParentState := activeParentState }⟩

#print axioms ParentwiseBadParentDualChildCertificate
#print axioms ParentwiseBadParentDualChildCertificate.qFibreChildDatum
#print axioms ParentwiseBadParentDualChildCertificate.activeParentChildDatum
#print axioms ParentwiseBadParentDualChildCertificate.qFibreChildAtom_radius
#print axioms ParentwiseBadParentDualChildCertificate.activeParentChildAtom_radius
#print axioms ParentwiseBadParentDualChildCertificate.qFibreChild_radius_eq_fixed_mul_ratio
#print axioms ParentwiseBadParentDualChildCertificate.qFibreChild_admissible
#print axioms ParentwiseBadParentDualChildCertificate.activeParentChild_admissible
#print axioms ParentwiseBadParentDualChildCertificate.qFibre_shadingMass_loss
#print axioms ParentwiseBadParentDualChildCertificate.activeParent_normalizedShadingMass_loss
#print axioms ParentwiseBadParentDualChildCertificate.activeParent_conflict_cap
#print axioms ParentwiseBadParentDualChildCertificate.activeParent_katzTao_at_scale
#print axioms ParentwiseBadParentDualChildCertificate.qFibre_successor_radiusProduct
#print axioms exists_parentwiseBadParentDualChildCertificate

end
end Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
