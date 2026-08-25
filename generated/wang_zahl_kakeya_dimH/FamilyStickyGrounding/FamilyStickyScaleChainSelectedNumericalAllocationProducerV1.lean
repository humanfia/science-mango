import FamilyStickyGrounding.FamilyStickyScaleChainDividingFiniteNodeProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainSelectedNumericalAllocationProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainExponentProductBudgetV1
open FamilyStickyScaleChainAdjacentUpperProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1

noncomputable section

/-!
# Selected-step numerical allocation producer

The exponent allocation structures prove two numerical inequalities before
the stopping endpoint uses them: an actual global product bound and an actual
adjacent-value bound.  On the dividing branch constructed in the preceding
module, only the selected first non-large interval is used.  Consequently the
strongest honest interface consists of exactly two decidable comparisons at
that interval.

This file supplies:

* zero-local-exponent producers for callers that still need the old allocation
  structures;
* a forgetful map from either allocation API to the two selected comparisons;
* an exact decidable verified-or-failed comparison search;
* unit-cap producers using only the sign of the reserved predecessor profile;
* a direct actual constant-bearing and recovered literal endpoint consuming
  the two comparisons instead of an exponent decomposition.

Small-delta absorption controls the later localization constant.  It cannot
repair a failed global or adjacent comparison; the strict reverse inequalities
below are therefore sharp allocation obstructions.
-/

variable {delta : NNReal} {outerDepth chainDepth adjacentDepth : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {A : ActualIntervalCovers S}
  {profile : Nat -> Real} {stage : Nat}

/-! ## Literal selected-step numerical quantities -/

def actualGlobalEndpointRatioAt
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) : ENNReal :=
  (MeasureTheory.volume ((B.datum m).testBody chainDepth : Set
      LeanEval.Analysis.WangZahlKakeya.Space) /
    MeasureTheory.volume ((B.datum m).testBody 0 : Set
      LeanEval.Analysis.WangZahlKakeya.Space)) *
    ((B.datum m).tubeVolume 0 / (B.datum m).tubeVolume chainDepth)

def actualGlobalProductAt
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) : ENNReal :=
  (∏ l ∈ Finset.range chainDepth,
    FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
      (B.hierarchy m) (B.datum m) l) *
    actualGlobalEndpointRatioAt B m

def requiredGlobalPowerAt
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) : ENNReal :=
  (S.theta m : ENNReal) ^ (-profile (stage - 1))

def requiredAdjacentPowerAt
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) : ENNReal :=
  (((S.theta m / S.tau m : NNReal) : ENNReal) ^
    profile (stage - 1))

/-- Exactly the two comparisons consumed at one selected stopping interval. -/
def SelectedNumericalBudgets
    (B : BufferedChainFamily outerDepth chainDepth)
    (A : ActualIntervalCovers S)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) : Prop :=
  actualGlobalProductAt B m <=
      requiredGlobalPowerAt S profile stage m ∧
    A.adjacentCoarseValue m <=
      requiredAdjacentPowerAt S profile stage m

/-- The selected budget is computationally decidable: it is a conjunction of
two comparisons in the linear order ENNReal. -/
def selectedNumericalBudgetsDecision
    (B : BufferedChainFamily outerDepth chainDepth)
    (A : ActualIntervalCovers S)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) :
    Decidable (SelectedNumericalBudgets B A profile stage m) := by
  change Decidable
    (actualGlobalProductAt B m <=
        requiredGlobalPowerAt S profile stage m ∧
      A.adjacentCoarseValue m <=
        requiredAdjacentPowerAt S profile stage m)
  infer_instance

/-! ## Old allocations automatically forget to numerical budgets -/

theorem selectedNumericalBudgets_of_exponentBudgetData
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage profile)
    (adjacentExponent :
      AdjacentBufferedHierarchyFamily.ExponentBudgetData G stage profile)
    (m : Fin outerDepth) :
    SelectedNumericalBudgets B A profile stage m := by
  constructor
  · simpa [actualGlobalProductAt, actualGlobalEndpointRatioAt,
      requiredGlobalPowerAt] using
      globalExponent.actualProductBudget B m
  · simpa [requiredAdjacentPowerAt] using
      adjacentExponent.adjacent_upper G m

theorem selectedNumericalBudgets_of_allocations
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (globalAllocation : GlobalExponentAllocation B S stage profile)
    (adjacentAllocation : AdjacentExponentAllocation G stage profile)
    (delta_pos : 0 < delta) (m : Fin outerDepth) :
    SelectedNumericalBudgets B A profile stage m :=
  selectedNumericalBudgets_of_exponentBudgetData B G
    (globalAllocation.toExponentBudgetData delta_pos)
    (adjacentAllocation.toExponentBudgetData delta_pos) m

/-! ## Explicit zero-local-exponent allocation producers -/

/-- No exponent functions or balance equation need be supplied when every
local global factor is bounded by one and the endpoint ratio carries the
entire required negative exponent. -/
def globalAllocation_of_zeroLocalExponents
    (B : BufferedChainFamily outerDepth chainDepth)
    (local_le_one : forall m l, l < chainDepth ->
      FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
        (B.hierarchy m) (B.datum m) l <= 1)
    (endpoint_le : forall m,
      actualGlobalEndpointRatioAt B m <=
        requiredGlobalPowerAt S profile stage m) :
    GlobalExponentAllocation B S stage profile where
  localExponent := fun _ _ => 0
  endpointExponent := fun _ => -profile (stage - 1)
  localFactor_upper := by
    intro m l hl
    simpa using local_le_one m l hl
  endpointRatio_upper := by
    intro m
    simpa [actualGlobalEndpointRatioAt, requiredGlobalPowerAt] using
      endpoint_le m
  exponent_balance := by
    intro m
    simp

/-- The analogous zero-local-exponent producer for the adjacent hierarchy. -/
def adjacentAllocation_of_zeroLocalExponents
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (local_le_one : forall m K hK l, l < adjacentDepth ->
      FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
        (G.hierarchy m) (G.datum m K hK) l <= 1)
    (endpoint_le : forall m K hK,
      G.endpointRatio m K hK <=
        requiredAdjacentPowerAt S profile stage m) :
    AdjacentExponentAllocation G stage profile where
  localExponent := fun _ _ _ => 0
  endpointExponent := fun _ _ => profile (stage - 1)
  localFactor_upper := by
    intro m K hK l hl
    simpa using local_le_one m K hK l hl
  endpointRatio_upper := by
    intro m K hK
    simpa [requiredAdjacentPowerAt] using endpoint_le m K hK
  exponent_balance := by
    intro m K
    simp

/-! ## Exact decidable failures and sharp obstructions -/

inductive SelectedNumericalBudgetFailure
    (B : BufferedChainFamily outerDepth chainDepth)
    (A : ActualIntervalCovers S)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) where
  | global (failed :
      requiredGlobalPowerAt S profile stage m <
        actualGlobalProductAt B m)
  | adjacent (failed :
      requiredAdjacentPowerAt S profile stage m <
        A.adjacentCoarseValue m)

/-- A proof-relevant executable search returns either both comparisons or the
first strict reverse inequality. -/
def selectedNumericalBudgetSearch
    (B : BufferedChainFamily outerDepth chainDepth)
    (A : ActualIntervalCovers S)
    (profile : Nat -> Real) (stage : Nat)
    (m : Fin outerDepth) :
    PLift (SelectedNumericalBudgets B A profile stage m) ⊕
      SelectedNumericalBudgetFailure B A profile stage m := by
  by_cases global_ok :
      actualGlobalProductAt B m <=
        requiredGlobalPowerAt S profile stage m
  · by_cases adjacent_ok :
        A.adjacentCoarseValue m <=
          requiredAdjacentPowerAt S profile stage m
    · exact Sum.inl ⟨global_ok, adjacent_ok⟩
    · exact Sum.inr (.adjacent (lt_of_not_ge adjacent_ok))
  · exact Sum.inr (.global (lt_of_not_ge global_ok))

theorem no_globalExponentBudgetData_of_selectedFailure
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth)
    (failed : requiredGlobalPowerAt S profile stage m <
      actualGlobalProductAt B m) :
    Not (Nonempty
      (FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage profile)) := by
  rintro ⟨E⟩
  exact (not_le_of_gt failed) (by
    simpa [actualGlobalProductAt, actualGlobalEndpointRatioAt,
      requiredGlobalPowerAt] using E.actualProductBudget B m)

theorem no_globalAllocation_of_selectedFailure
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) (delta_pos : 0 < delta)
    (failed : requiredGlobalPowerAt S profile stage m <
      actualGlobalProductAt B m) :
    Not (Nonempty (GlobalExponentAllocation B S stage profile)) := by
  rintro ⟨E⟩
  exact no_globalExponentBudgetData_of_selectedFailure B m failed
    ⟨E.toExponentBudgetData delta_pos⟩

theorem no_adjacentExponentBudgetData_of_selectedFailure
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (m : Fin outerDepth)
    (failed : requiredAdjacentPowerAt S profile stage m <
      A.adjacentCoarseValue m) :
    Not (Nonempty
      (AdjacentBufferedHierarchyFamily.ExponentBudgetData
        G stage profile)) := by
  rintro ⟨E⟩
  exact (not_le_of_gt failed) (by
    simpa [requiredAdjacentPowerAt] using E.adjacent_upper G m)

theorem no_adjacentAllocation_of_selectedFailure
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (m : Fin outerDepth) (delta_pos : 0 < delta)
    (failed : requiredAdjacentPowerAt S profile stage m <
      A.adjacentCoarseValue m) :
    Not (Nonempty (AdjacentExponentAllocation G stage profile)) := by
  rintro ⟨E⟩
  exact no_adjacentExponentBudgetData_of_selectedFailure G m failed
    ⟨E.toExponentBudgetData delta_pos⟩

/-! ## Automatic unit-cap numerical producer -/

theorem selectedNumericalBudgets_of_unitCaps
    (B : BufferedChainFamily outerDepth chainDepth)
    (A : ActualIntervalCovers S)
    (m : Fin outerDepth)
    (profile_pred_nonneg : 0 <= profile (stage - 1))
    (delta_pos : 0 < delta)
    (global_product_le_one : actualGlobalProductAt B m <= 1)
    (adjacent_value_le_one : A.adjacentCoarseValue m <= 1) :
    SelectedNumericalBudgets B A profile stage m := by
  have theta_le_one : (S.theta m : ENNReal) <= 1 := by
    exact_mod_cast S.theta_le_one m
  have theta_power_le_one :
      (S.theta m : ENNReal) ^ profile (stage - 1) <= 1 :=
    ENNReal.rpow_le_one theta_le_one profile_pred_nonneg
  have one_le_global :
      1 <= requiredGlobalPowerAt S profile stage m := by
    rw [requiredGlobalPowerAt, ENNReal.rpow_neg]
    exact ENNReal.one_le_inv.2 theta_power_le_one
  have tau_pos : 0 < S.tau m :=
    delta_pos.trans_le (S.delta_le_tau m)
  have one_le_ratio_nn : 1 <= S.theta m / S.tau m :=
    (one_le_div tau_pos).2 (S.tau_le_theta m)
  have one_le_ratio :
      (1 : ENNReal) <=
        ((S.theta m / S.tau m : NNReal) : ENNReal) := by
    exact_mod_cast one_le_ratio_nn
  have one_le_adjacent :
      1 <= requiredAdjacentPowerAt S profile stage m := by
    have hpow := ENNReal.rpow_le_rpow_of_exponent_le
      one_le_ratio profile_pred_nonneg
    simpa [requiredAdjacentPowerAt] using hpow
  exact ⟨global_product_le_one.trans one_le_global,
    adjacent_value_le_one.trans one_le_adjacent⟩

theorem reserveTailLoss_pred_nonneg
    {eta : Nat -> Real} {stage : Nat} {loss : Real}
    (stage_pos : 1 <= stage)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0) :
    0 <= reserveTailLoss eta stage loss (stage - 1) := by
  rw [reserveTailLoss_pred eta stage_pos loss]
  have eta_zero_le : eta 0 <= eta (stage - 1) :=
    eta_monotone (Nat.zero_le _)
  linarith

/-! ## Direct selected numerical endpoint -/

variable {N : Nat} {epsilon : Real}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The direct constant-bearing witness reads only the two selected numerical
comparisons and the selected finite-node checks. -/
noncomputable def constantWitnessAtNonLargeStep_of_numericalBudgets
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (profile_stage_le_epsilon : profile stage <= epsilon)
    (m : Fin outerDepth) (not_large : Not (S.IsLarge epsilon m))
    (budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S) profile stage m)
    (V : VerifiedStepNodeLowerBounds
      (eta := profile) (stage := stage)
      (C.toActualIntervalCovers S) R m)
    (two_le_profile : (2 : Real) <= profile stage)
    (delta_pos : 0 < delta) :
    KatzTaoConstantDividingWitness delta N epsilon profile
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
    exact V.actual_buffered_lower_with_constant
      (fun n => delta_pos.trans_le (S.delta_le_tau n))
      two_le_profile profile_stage_le_epsilon rho ⟨lower, upper⟩

variable {eta : Nat -> Real}

/-- Final recovered endpoint with no global or adjacent allocation argument.
The two explicit comparisons are taken at the computed first non-large step. -/
theorem exists_recoveredLiteralWitness_of_selectedNumericalBudgets
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S)
      (reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (oneBasedStage slot)
      (firstNonLargeStep S epsilon not_all_large))
    (V : VerifiedStepNodeLowerBounds
      (eta := reserveTailLoss eta (oneBasedStage slot)
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
  let loss : Real :=
    halfReservedExponentRoom eta (oneBasedStage slot) epsilon
  let reservedProfile : Nat -> Real :=
    reserveTailLoss eta (oneBasedStage slot) loss
  have room : eta (oneBasedStage slot) + loss <= epsilon :=
    eta_add_halfReservedExponentRoom_le strict_room
  have reserved_stage_le :
      reservedProfile (oneBasedStage slot) <= epsilon :=
    reserveTailLoss_stage_le room
  have two_le_reserved :
      (2 : Real) <= reservedProfile (oneBasedStage slot) := by
    have h := two_le_add_halfReservedExponentRoom_of_two_le_zero
      eta_monotone two_le_zero strict_room
    simpa [reservedProfile, loss] using h
  let W : KatzTaoConstantDividingWitness delta N epsilon reservedProfile
      (actualStrictLocalizationConstant iota) :=
    constantWitnessAtNonLargeStep_of_numericalBudgets
      C R B (oneBasedStage slot) (oneBasedStage_pos slot)
        (oneBasedStage_le slot) reserved_stage_le
        (firstNonLargeStep S epsilon not_all_large)
        (firstNonLargeStep_not_large S epsilon not_all_large)
        budgets V two_le_reserved delta_pos
  have epsilon_pos : 0 < epsilon := by
    have eta_zero_le_stage : eta 0 <= eta (oneBasedStage slot) :=
      eta_monotone (Nat.zero_le _)
    linarith
  have W_tau_pos : 0 < W.tau :=
    delta_pos.trans_le W.delta_le_tau
  exact exists_literalWitness_for_halfRoomRecoveredProfile
    (eta := eta) (stage := oneBasedStage slot) W rfl
      (actualStrictLocalizationConstant_ne_top iota)
      epsilon_pos strict_room delta_pos W_tau_pos delta_le

/-- A fully numerical specialization: unit caps automatically generate both
selected power comparisons from the reserved predecessor exponent sign. -/
theorem exists_recoveredLiteralWitness_of_selectedUnitCaps
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (global_product_le_one :
      actualGlobalProductAt B
        (firstNonLargeStep S epsilon not_all_large) <= 1)
    (adjacent_value_le_one :
      (C.toActualIntervalCovers S).adjacentCoarseValue
        (firstNonLargeStep S epsilon not_all_large) <= 1)
    (V : VerifiedStepNodeLowerBounds
      (eta := reserveTailLoss eta (oneBasedStage slot)
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
  have pred_nonneg :
      0 <=
        reserveTailLoss eta (oneBasedStage slot)
          (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)
          (oneBasedStage slot - 1) :=
    reserveTailLoss_pred_nonneg (oneBasedStage_pos slot)
      eta_monotone two_le_zero
  have budgets := selectedNumericalBudgets_of_unitCaps
    B (C.toActualIntervalCovers S)
      (firstNonLargeStep S epsilon not_all_large)
      pred_nonneg delta_pos global_product_le_one adjacent_value_le_one
  exact exists_recoveredLiteralWitness_of_selectedNumericalBudgets
    C R B slot eta_monotone two_le_zero strict_room not_all_large
      budgets V delta_pos delta_le

#print axioms selectedNumericalBudgetsDecision
#print axioms selectedNumericalBudgets_of_exponentBudgetData
#print axioms selectedNumericalBudgets_of_allocations
#print axioms globalAllocation_of_zeroLocalExponents
#print axioms adjacentAllocation_of_zeroLocalExponents
#print axioms selectedNumericalBudgetSearch
#print axioms no_globalExponentBudgetData_of_selectedFailure
#print axioms no_globalAllocation_of_selectedFailure
#print axioms no_adjacentExponentBudgetData_of_selectedFailure
#print axioms no_adjacentAllocation_of_selectedFailure
#print axioms selectedNumericalBudgets_of_unitCaps
#print axioms reserveTailLoss_pred_nonneg
#print axioms constantWitnessAtNonLargeStep_of_numericalBudgets
#print axioms exists_recoveredLiteralWitness_of_selectedNumericalBudgets
#print axioms exists_recoveredLiteralWitness_of_selectedUnitCaps

end
end FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
