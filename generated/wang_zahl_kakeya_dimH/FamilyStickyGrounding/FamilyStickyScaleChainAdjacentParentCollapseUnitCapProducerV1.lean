import FamilyStickyGrounding.FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainAdjacentParentCollapseUnitCapProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainActualUnitCapProducerV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1
open FamilyStickyScaleChainHierarchySiblingRigidityV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-!
# Adjacent unit cap from collapse of the actual parent image

The stopping rule selects only a scale interval.  The additional structural
input isolated here says that the literal parent map of the actual adjacent
cover has subsingleton image on active fine occurrences.  Parent surjectivity
then makes the whole active coarse set subsingleton, which supplies the unit
cap consumed by the recovered Family7 endpoint.

For the canonical selected identity cover the active parents retain every
selected level-zero occurrence.  Its exact cardinality is therefore the
cardinality of the selected source, recording why collapse is not automatic.
-/

universe u

variable {delta rho : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Generic finite parent-image collapse -/

/-- The literal parent image on active fine occurrences is subsingleton. -/
def ActiveParentImageCollapse (Q : StickyScaleCover fine rho) : Prop :=
  forall i, i ∈ Q.activeFine -> forall j, j ∈ Q.activeFine ->
    Q.parent i = Q.parent j

/-- Surjectivity of a sticky cover's parent map transports parent-image
collapse to cardinality at most one of its actual active coarse set. -/
theorem activeCoarse_card_le_one_of_parentImageCollapse
    (Q : StickyScaleCover fine rho)
    (hcollapse : ActiveParentImageCollapse Q) :
    Q.activeCoarse.card <= 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨i, hi, hip⟩ := Q.parent_surjective p hp
  obtain ⟨j, hj, hjq⟩ := Q.parent_surjective q hq
  rw [← hip, ← hjq]
  exact hcollapse i hi j hj

/-! ## The first non-large actual adjacent cover -/

variable {depth : Nat}

/-- Parent-image collapse specialized to the literal adjacent cover selected
by `firstNonLargeStep`. -/
def FirstNonLargeActualAdjacentParentCollapse
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (not_all_large : Not (S.AllStepsLarge epsilon)) : Prop :=
  ActiveParentImageCollapse
    (actualAdjacentScaleCover (C.toActualIntervalCovers S)
      (firstNonLargeStep S epsilon not_all_large))

/-- The specialized collapse certificate supplies exactly the active-card
hypothesis used by the adjacent unit-cap producer. -/
theorem firstNonLarge_actualAdjacent_activeCoarse_card_le_one_of_parentCollapse
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (hcollapse :
      FirstNonLargeActualAdjacentParentCollapse C S epsilon not_all_large) :
    (actualAdjacentScaleCover (C.toActualIntervalCovers S)
      (firstNonLargeStep S epsilon not_all_large)).activeCoarse.card <= 1 := by
  exact activeCoarse_card_le_one_of_parentImageCollapse _ hcollapse

/-! ## Recovered endpoint and search wrappers -/

variable {outerDepth chainDepth N : Nat} {epsilon : Real}
  {eta : Nat -> Real}
  {S : FiniteScaleSequence delta outerDepth}

/-- The recovered endpoint with the literal adjacent parent-collapse
certificate in place of an exposed active-coarse cardinality hypothesis. -/
theorem exists_recoveredLiteralWitness_of_actualGlobalCaps_parentCollapse_and_relevantNodes
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalCaps : ActualGlobalFactorCaps B
      (firstNonLargeStep S epsilon not_all_large))
    (parentCollapse :
      FirstNonLargeActualAdjacentParentCollapse C S epsilon not_all_large)
    (V : VerifiedRelevantStepNodeLowerBounds
      (epsilon := epsilon)
      (profile := reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (stage := oneBasedStage slot)
      (C.toActualIntervalCovers S) R
        (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))) := by
  exact exists_recoveredLiteralWitness_of_actualUnitCaps_and_relevantNodes
    C R B slot eta_monotone two_le_zero strict_room not_all_large globalCaps
      (firstNonLarge_actualAdjacent_activeCoarse_card_le_one_of_parentCollapse
        C S epsilon not_all_large parentCollapse)
      V delta_pos delta_le

/-- The relevant-node finite search with parent collapse replacing its raw
active-cardinality input. -/
noncomputable def recoveredLiteralWitnessOrFirstRelevantNodeAlternative_of_parentCollapse
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalCaps : ActualGlobalFactorCaps B
      (firstNonLargeStep S epsilon not_all_large))
    (parentCollapse :
      FirstNonLargeActualAdjacentParentCollapse C S epsilon not_all_large)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    PLift (Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)))) ⊕
      FirstRelevantNodeAnalyticAlternative
        (epsilon := epsilon)
        (profile := reserveTailLoss eta (oneBasedStage slot)
          (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
        (stage := oneBasedStage slot)
        (C.toActualIntervalCovers S) R
          (firstNonLargeStep S epsilon not_all_large) :=
  recoveredLiteralWitnessOrFirstRelevantNodeAlternative
    C R B slot eta_monotone two_le_zero strict_room not_all_large globalCaps
      (firstNonLarge_actualAdjacent_activeCoarse_card_le_one_of_parentCollapse
        C S epsilon not_all_large parentCollapse)
      delta_pos delta_le

/-! ## Exact selected-identity cardinality -/

variable {nominalRadius : Nat -> NNReal} {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-- The canonical all-radius selected identity cover retains every selected
level-zero occurrence at every adjacent upper endpoint. -/
theorem selectedIdentity_actualAdjacent_activeCoarse_card_eq_selected_card
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (T : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    (m : Fin depth) :
    (actualAdjacentScaleCover
      ((selectedIdentityCoherentCover R).toActualIntervalCovers T) m).activeCoarse.card =
      R.selected.card := by
  simp [actualAdjacentScaleCover, selectedIdentityCoherentCover,
    identityRadiusCoherentCover, identityRadiusScaleCover,
    CoherentStickyMultiscaleCover.toActualIntervalCovers,
    CoherentStickyMultiscaleCover.intervalMultiscaleCover,
    CoherentStickyMultiscaleCover.intervalScaleCover,
    MultiscaleTubeHierarchy.effectiveFamily, selectedHierarchy,
    selectedHierarchyFamily, UniformTubeFamily.buffer,
    UniformTubeFamily.restrictTo]
  change (Finset.univ : Finset {i // i ∈ R.selected}).card = R.selected.card
  simp

/-- Consequently the desired unit-cardinality condition for the selected
identity cover is exactly a unit-cardinality condition on the selected source;
the canonical cover alone does not manufacture it. -/
theorem selectedIdentity_actualAdjacent_activeCoarse_card_le_one_iff
    (R : SelectedTerminalSourceChartBucketGeometry (H := H))
    (T : FiniteScaleSequence
      ((selectedHierarchy R).effectiveRadius 0) depth)
    (m : Fin depth) :
    (actualAdjacentScaleCover
      ((selectedIdentityCoherentCover R).toActualIntervalCovers T) m).activeCoarse.card <= 1 ↔
      R.selected.card <= 1 := by
  rw [selectedIdentity_actualAdjacent_activeCoarse_card_eq_selected_card]

#print axioms ActiveParentImageCollapse
#print axioms activeCoarse_card_le_one_of_parentImageCollapse
#print axioms FirstNonLargeActualAdjacentParentCollapse
#print axioms firstNonLarge_actualAdjacent_activeCoarse_card_le_one_of_parentCollapse
#print axioms exists_recoveredLiteralWitness_of_actualGlobalCaps_parentCollapse_and_relevantNodes
#print axioms recoveredLiteralWitnessOrFirstRelevantNodeAlternative_of_parentCollapse
#print axioms selectedIdentity_actualAdjacent_activeCoarse_card_eq_selected_card
#print axioms selectedIdentity_actualAdjacent_activeCoarse_card_le_one_iff

end
end FamilyStickyScaleChainAdjacentParentCollapseUnitCapProducerV1
