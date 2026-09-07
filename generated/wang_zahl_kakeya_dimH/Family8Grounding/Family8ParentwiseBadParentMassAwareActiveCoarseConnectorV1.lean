import Family8Grounding.Family8ParentwiseBadParentActualFactorListSuccessorV1
import Family8Grounding.Family8ParentwiseBadParentFactorListStateV1
import Mathlib.Tactic

/-!
# Active-coarse admissibility carried by the mass-aware factor state

The mass-aware successor list uses the literal parent-aggregated active coarse
datum, but packaging an `ActualFactorDatum` does not by itself prove that datum
admissible.  This connector records the separate eighth-normalized admissible
active-coarse child produced by the fresh selector.

Both analytic obligations needed by that selector are named fields of the
state: the normalized conflict cap and the active-coarse Katz--Tao estimate.
The selected set and every card, mass, Katz--Tao, and average loss are retained.
No callback is stored and the existing factor-list modules are unchanged.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentMassAwareActiveCoarseConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorListStateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8StickyActiveCoarseAdmissibleChildV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-! ## The active-coarse analytic component -/

/-- The explicit obligations and concrete output of the active-coarse fresh
selector.  In particular, the conflict and Katz--Tao inputs remain accessible
after the state has been constructed. -/
structure ActiveCoarseAdmissibleFactorState
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (conflictThreshold : Nat) (activeC : ENNReal) where
  conflict_cap : forall a : {k // k ∈ S.activeCoarse},
    (normalizedConflictIndices
      (activeCoarseAggregatedDatum D S) a).card <= conflictThreshold
  katzTao_at_scale : S.IsKatzTaoAtScale activeC
  selected : Finset {k // k ∈ S.activeCoarse}
  selected_nonempty : selected.Nonempty
  child_admissible :
    (activeCoarseFreshChildDatum D S selected).IsAdmissible
  card_loss :
    (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) <=
      (conflictThreshold + 1 : Nat) * (selected.card : ENNReal)
  normalized_mass_loss :
    (eighthNormalizedDatum
      (activeCoarseAggregatedDatum D S)).shading.shadingMass <=
        (conflictThreshold + 1 : Nat) *
          (activeCoarseFreshChildDatum D S selected).shading.shadingMass
  child_katzTao :
    IsKatzTao (128 * activeC)
      (activeCoarseFreshChildDatum D S selected).family.bodyFamily
  average_loss :
    (activeCoarseAggregatedDatum D S).shading.averageMultiplicity <=
      (conflictThreshold + 1 : Nat) *
        (activeCoarseFreshChildDatum D S selected).shading.averageMultiplicity

/-- The active-coarse producer, with its two analytic obligations explicit in
the theorem arguments and copied into the resulting state. -/
theorem exists_activeCoarseAdmissibleFactorState
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrhoPos : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hrhoSixteenth : rho <= (1 / 16 : NNReal))
    (hactive : S.activeCoarse.Nonempty)
    (conflictThreshold : Nat)
    (hconflict : forall a : {k // k ∈ S.activeCoarse},
      (normalizedConflictIndices
        (activeCoarseAggregatedDatum D S) a).card <= conflictThreshold)
    (activeC : ENNReal) (hKT : S.IsKatzTaoAtScale activeC) :
    Nonempty (ActiveCoarseAdmissibleFactorState
      D S conflictThreshold activeC) := by
  obtain ⟨selected, hselected, hadmissible, hcard, hmass, hchildKT,
      havg⟩ :=
    exists_activeCoarse_admissibleChild D hD S hrhoPos hrhoHalf
      hrhoSixteenth hactive hconflict hKT
  exact ⟨
    { conflict_cap := hconflict
      katzTao_at_scale := hKT
      selected := selected
      selected_nonempty := hselected
      child_admissible := hadmissible
      card_loss := hcard
      normalized_mass_loss := hmass
      child_katzTao := hchildKT
      average_loss := havg }⟩

/-! ## Joint parentwise and active-coarse state -/

/-- The existing literal parentwise factor state together with the independent
admissible active-coarse child required to continue recursively. -/
structure ParentwiseBadParentMassAwareActiveCoarseState
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (lower factorC : ENNReal)
    (conflictThreshold : Nat) (activeC : ENNReal) where
  parentwise : ParentwiseBadParentFactorListState
    D S left right hrho hrhoOne q lower factorC
  activeCoarse : ActiveCoarseAdmissibleFactorState
    D S conflictThreshold activeC

namespace ParentwiseBadParentMassAwareActiveCoarseState

variable {D : ActualTubeDatum delta iota}
  {S : StickyScaleCover D.family rho}
  {left right : List ActualFactorDatum}
  {hrho : 0 < rho} {hrhoOne : rho <= 1}
  {q : {q // q ∈ S.activeCoarse}}
  {lower factorC activeC : ENNReal} {conflictThreshold : Nat}

/-- The actual source list associated with the joint state. -/
def sourceFactors
    (_X : ParentwiseBadParentMassAwareActiveCoarseState
      D S left right hrho hrhoOne q lower factorC conflictThreshold activeC) :
    List ActualFactorDatum :=
  badParentSourceFactorList D left right S

/-- The actual mass-aware successor list uses the selected fibre stored in the
parentwise component. -/
def successorFactors
    (X : ParentwiseBadParentMassAwareActiveCoarseState
      D S left right hrho hrhoOne q lower factorC conflictThreshold activeC) :
    List ActualFactorDatum :=
  badParentSuccessorFactorList
    D left right S hrho hrhoOne q X.parentwise.selected

/-- The separately selected admissible normalized active-coarse factor that is
available for the next recursive step. -/
def nextActiveCoarseAtom
    (X : ParentwiseBadParentMassAwareActiveCoarseState
      D S left right hrho hrhoOne q lower factorC conflictThreshold activeC) :
    ActualFactorDatum :=
  ActualFactorDatum.ofDatum
    (activeCoarseFreshChildDatum D S X.activeCoarse.selected)

@[simp] theorem nextActiveCoarseAtom_radius
    (X : ParentwiseBadParentMassAwareActiveCoarseState
      D S left right hrho hrhoOne q lower factorC conflictThreshold activeC) :
    X.nextActiveCoarseAtom.radius = rho / 8 :=
  rfl

theorem nextActiveCoarseAtom_admissible
    (X : ParentwiseBadParentMassAwareActiveCoarseState
      D S left right hrho hrhoOne q lower factorC conflictThreshold activeC) :
    (activeCoarseFreshChildDatum
      D S X.activeCoarse.selected).IsAdmissible :=
  X.activeCoarse.child_admissible

/-- Existing exact scale accounting remains valid for the mass-aware list. -/
theorem successor_radiusProduct
    (X : ParentwiseBadParentMassAwareActiveCoarseState
      D S left right hrho hrhoOne q lower factorC conflictThreshold activeC) :
    factorRadiusProduct X.successorFactors =
      (3 / 64 : NNReal) * factorRadiusProduct X.sourceFactors := by
  exact badParentSuccessorFactorList_radiusProduct
    D left right S hrho hrhoOne q X.parentwise.selected

/-- Existing forward cardinality accounting is transported from the concrete
parentwise certificate, not postulated again. -/
theorem successor_cardProduct_le
    (X : ParentwiseBadParentMassAwareActiveCoarseState
      D S left right hrho hrhoOne q lower factorC conflictThreshold activeC) :
    factorCardProduct X.successorFactors <=
      factorC * factorCardProduct X.sourceFactors := by
  exact badParentSuccessorFactorList_cardProduct_le
    D left right S hrho hrhoOne q X.parentwise.selected lower factorC
      X.parentwise.product

end ParentwiseBadParentMassAwareActiveCoarseState

/-! ## Callback-free joint producer -/

/-- Construct both components.  The parentwise bad-fibre assumptions feed the
existing factor state, while the conflict cap and active KT estimate feed the
new active-coarse component.  Neither pair is hidden behind a callback. -/
theorem exists_parentwiseBadParentMassAwareActiveCoarseState
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
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
    Nonempty (ParentwiseBadParentMassAwareActiveCoarseState
      D S left right hrho hrhoOne q lower factorC
        conflictThreshold activeC) := by
  obtain ⟨parentwise⟩ := exists_parentwiseBadParentFactorListState
    D S left right hD hrho hrhoOne hdeltaRho q hlowerTop hbad huniform
  obtain ⟨activeCoarse⟩ := exists_activeCoarseAdmissibleFactorState
    D hD S hrho hrhoHalf hrhoSixteenth ⟨q.1, q.2⟩
      conflictThreshold hconflict activeC hKT
  exact ⟨{ parentwise := parentwise, activeCoarse := activeCoarse }⟩

#print axioms ActiveCoarseAdmissibleFactorState
#print axioms exists_activeCoarseAdmissibleFactorState
#print axioms ParentwiseBadParentMassAwareActiveCoarseState
#print axioms ParentwiseBadParentMassAwareActiveCoarseState.sourceFactors
#print axioms ParentwiseBadParentMassAwareActiveCoarseState.successorFactors
#print axioms ParentwiseBadParentMassAwareActiveCoarseState.nextActiveCoarseAtom
#print axioms ParentwiseBadParentMassAwareActiveCoarseState.nextActiveCoarseAtom_admissible
#print axioms ParentwiseBadParentMassAwareActiveCoarseState.successor_radiusProduct
#print axioms ParentwiseBadParentMassAwareActiveCoarseState.successor_cardProduct_le
#print axioms exists_parentwiseBadParentMassAwareActiveCoarseState

end
end Family8ParentwiseBadParentMassAwareActiveCoarseConnectorV1
