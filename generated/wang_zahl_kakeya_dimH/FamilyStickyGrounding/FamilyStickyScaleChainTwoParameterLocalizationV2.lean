import FamilyStickyGrounding.FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainTwoParameterLocalizationV2

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
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1.CoherentStickyMultiscaleCover
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1

noncomputable section

variable {delta : NNReal} {depth : Nat}
  {gapEpsilon : Real} {profile : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-!
# Two-parameter strict localization

The scale-gap parameter used by `IsLarge` and `IsBuffered` is independent of
the target exponent profile.  The concrete localization proof only needs the
gap to be nonnegative; its exponent estimate still needs the target profile
to be at least two.  This module records that separation without introducing
a second witness structure.
-/

namespace CoherentIntervalLocalizationGeometry

variable {C : CoherentStickyMultiscaleCover fine}
  {R : IntervalRootedRefinementScaleTree S}

/-- Actual local geometry gives strict constant-bearing localization when the
scale-gap parameter is merely nonnegative.  No comparison between the target
exponent and the scale-gap parameter is used. -/
theorem toActualStrictConstantLocatedCoarseValueLocalization_of_gap_nonneg
    (tau_pos : forall m, 0 < S.tau m)
    (two_le_profile : (2 : Real) <= profile stage)
    (gap_nonneg : 0 <= gapEpsilon) :
    StrictConstantLocatedCoarseValueLocalization
      (epsilon := gapEpsilon) (eta := profile) (stage := stage)
      (C.toActualIntervalCovers S) R
      (actualStrictLocalizationConstant iota) where
  localized_le := by
    intro m rho buffered strict
    let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
    have sigma_interval :=
      R.located_scale_mem_interval gap_nonneg m rho buffered
    have rho_le_one := le_one_of_isBuffered gap_nonneg m rho buffered
    let D :=
      FamilyStickyScaleChainCoherentLocalGeometryProducerV1.CoherentIntervalLocalizationGeometry.ofActualLocalGeometry
        C S tau_pos
    have geometry_bound :=
      toActualIntervalCovers_coarseValueAt_le_of_nestedGeometry C S m
        sigma rho sigma_interval.1 sigma_interval.2 rho_le_one
        (D.massLoss m sigma rho) (D.bodyLoss m sigma rho)
        (D.parentFiberMass m sigma rho sigma_interval.1 sigma_interval.2 rho_le_one)
        (D.capturingThickening m sigma rho sigma_interval.1 sigma_interval.2 rho_le_one)
    have loss_bound := actualLocalLoss_le_strictConstant_mul_scaleRatio_rpow
      C S tau_pos two_le_profile m sigma_interval.1 sigma_interval.2 rho_le_one
    exact geometry_bound.trans (mul_le_mul' loss_bound le_rfl)

end CoherentIntervalLocalizationGeometry

/-! ## Relevant-node consumer -/

namespace VerifiedRelevantStepNodeLowerBounds

variable {C : CoherentStickyMultiscaleCover fine}
  {R : IntervalRootedRefinementScaleTree S}
  {m : Fin depth}

/-- Relevant tree-node checks imply the actual buffered lower bound using
only nonnegativity of the scale-gap parameter. -/
theorem actual_buffered_lower_with_constant_of_gap_nonneg
    (V : VerifiedRelevantStepNodeLowerBounds
      (epsilon := gapEpsilon) (profile := profile) (stage := stage)
      (C.toActualIntervalCovers S) R m)
    (tau_pos : forall n, 0 < S.tau n)
    (two_le_profile : (2 : Real) <= profile stage)
    (gap_nonneg : 0 <= gapEpsilon)
    (rho : NNReal) (buffered : S.IsBuffered gapEpsilon m rho) :
    splitThreshold S profile stage m rho <=
      actualStrictLocalizationConstant iota *
        (C.toActualIntervalCovers S).coarseValueAt m rho := by
  have profile_nonneg : (0 : Real) <= profile stage :=
    (by norm_num : (0 : Real) <= 2).trans two_le_profile
  let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
  have sigma_interval :=
    R.located_scale_mem_interval gap_nonneg m rho buffered
  have sigma_pos : 0 < sigma := (R.tau_pos m).trans_le sigma_interval.1
  have rho_pos : 0 < rho := sigma_pos.trans_le sigma_interval.2
  have node_checked : splitThreshold S profile stage m sigma <=
      (C.toActualIntervalCovers S).coarseValueAt m sigma :=
    V.checked (R.tree.locate m rho)
      (locatedNode_isRelevant R gap_nonneg m rho buffered)
  let L : StrictConstantLocatedCoarseValueLocalization
      (epsilon := gapEpsilon) (eta := profile) (stage := stage)
      (C.toActualIntervalCovers S) R
        (actualStrictLocalizationConstant iota) :=
    CoherentIntervalLocalizationGeometry.toActualStrictConstantLocatedCoarseValueLocalization_of_gap_nonneg
      (C := C) (R := R) tau_pos two_le_profile gap_nonneg
  rcases lt_or_eq_of_le sigma_interval.2 with strict | equal
  · exact splitThreshold_le_constant_mul_of_located_coarseValue
      (C.toActualIntervalCovers S) m sigma rho sigma_pos rho_pos
      profile_nonneg (actualStrictLocalizationConstant iota)
      node_checked (L.localized_le m rho buffered strict)
  · have sigma_eq : sigma = rho := by
      simpa [sigma] using equal
    rw [<- sigma_eq]
    calc
      splitThreshold S profile stage m sigma <=
          (C.toActualIntervalCovers S).coarseValueAt m sigma := node_checked
      _ = 1 * (C.toActualIntervalCovers S).coarseValueAt m sigma := by simp
      _ <= actualStrictLocalizationConstant iota *
          (C.toActualIntervalCovers S).coarseValueAt m sigma :=
        mul_le_mul' (one_le_actualStrictLocalizationConstant iota) le_rfl

end VerifiedRelevantStepNodeLowerBounds

/-! ## Existing constant witness with separated parameters -/

variable {outerDepth chainDepth N : Nat}
  {S : FiniteScaleSequence delta outerDepth}

/-- The V1 constant-bearing witness already has the right shape for two
parameters: `gapEpsilon` controls the scale predicates, while `profile`
controls the numerical powers. -/
noncomputable def constantWitnessAtNonLargeStep_twoParameter
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (gap_nonneg : 0 <= gapEpsilon)
    (m : Fin outerDepth) (not_large : Not (S.IsLarge gapEpsilon m))
    (budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S) profile stage m)
    (V : VerifiedRelevantStepNodeLowerBounds
      (epsilon := gapEpsilon) (profile := profile) (stage := stage)
      (C.toActualIntervalCovers S) R m)
    (two_le_profile : (2 : Real) <= profile stage)
    (delta_pos : 0 < delta) :
    KatzTaoConstantDividingWitness delta N gapEpsilon profile
      (actualStrictLocalizationConstant iota) where
  tau := S.tau m
  theta := S.theta m
  stage := stage
  stage_pos := stage_pos
  stage_le := stage_le
  delta_le_tau := S.delta_le_tau m
  tau_le_theta := S.tau_le_theta m
  theta_le_one := S.theta_le_one m
  long := le_of_not_ge not_large
  globalValue := (B.finiteChain m).deltaMax 0
  adjacentValue := (C.toActualIntervalCovers S).adjacentCoarseValue m
  middleValue := (C.toActualIntervalCovers S).coarseValueAt m
  global_upper := by
    exact FiniteDeltaMaxChain.global_le_exponent_of_productBudget
      (B.finiteChain m) (S.theta m) (profile (stage - 1))
      (FamilyStickyScaleChainFiniteDeltaMaxBridgeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.productBudget_of_local_endpoint_le
        (B.datum m) (requiredGlobalPowerAt S profile stage m)
        (by
          simpa [actualGlobalProductAt, actualGlobalEndpointRatioAt] using
            budgets.1))
  adjacent_upper := by
    simpa [requiredAdjacentPowerAt] using budgets.2
  middle_lower_with_constant := by
    intro rho lower upper
    exact
      VerifiedRelevantStepNodeLowerBounds.actual_buffered_lower_with_constant_of_gap_nonneg
        V (fun n => delta_pos.trans_le (S.delta_le_tau n))
        two_le_profile gap_nonneg rho ⟨lower, upper⟩

#print axioms CoherentIntervalLocalizationGeometry.toActualStrictConstantLocatedCoarseValueLocalization_of_gap_nonneg
#print axioms VerifiedRelevantStepNodeLowerBounds.actual_buffered_lower_with_constant_of_gap_nonneg
#print axioms constantWitnessAtNonLargeStep_twoParameter

end
end FamilyStickyScaleChainTwoParameterLocalizationV2
