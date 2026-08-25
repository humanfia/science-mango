import FamilyStickyGrounding.FamilyStickyScaleChainActualStoppingUpstreamClosureV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainDividingFiniteNodeProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
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
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1

noncomputable section

/-!
# Dividing-branch finite-node producer

A non-large interval is selected only from its endpoint scales, whereas
VerifiedTreeNodeLowerBounds compares actual concentration with a threshold at
every tree node.  This module makes the separation exact.  It computes the
first non-large interval, gives a verified-or-failed-node finite search, and
shows when local checks can produce the old global certificate.  In the
general dividing branch, local checks at the selected interval directly
construct the actual constant-bearing witness and feed small-delta recovery.
-/

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {eta : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}

/-! ## The actual first non-large interval -/

noncomputable def nonLargeSteps
    (S : FiniteScaleSequence delta depth) (epsilon : Real) :
    Finset (Fin depth) := by
  classical
  exact Finset.univ.filter fun m => Not (S.IsLarge epsilon m)

@[simp] theorem mem_nonLargeSteps
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (m : Fin depth) :
    m ∈ nonLargeSteps S epsilon ↔ Not (S.IsLarge epsilon m) := by
  classical
  simp [nonLargeSteps]

theorem nonLargeSteps_nonempty_iff
    (S : FiniteScaleSequence delta depth) (epsilon : Real) :
    (nonLargeSteps S epsilon).Nonempty ↔
      Not (S.AllStepsLarge epsilon) := by
  classical
  constructor
  · rintro ⟨m, hm⟩ hall
    exact ((mem_nonLargeSteps S epsilon m).1 hm) (hall m)
  · intro hnot
    have exists_not_large :
        exists m, Not (S.IsLarge epsilon m) := by
      by_contra no_failure
      apply hnot
      intro m
      by_contra hm
      exact no_failure ⟨m, hm⟩
    obtain ⟨m, hm⟩ := exists_not_large
    exact ⟨m, (mem_nonLargeSteps S epsilon m).2 hm⟩

noncomputable def firstNonLargeStep
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (not_all_large : Not (S.AllStepsLarge epsilon)) : Fin depth :=
  (nonLargeSteps S epsilon).min'
    ((nonLargeSteps_nonempty_iff S epsilon).2 not_all_large)

theorem firstNonLargeStep_not_large
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (not_all_large : Not (S.AllStepsLarge epsilon)) :
    Not (S.IsLarge epsilon
      (firstNonLargeStep S epsilon not_all_large)) := by
  exact (mem_nonLargeSteps S epsilon _).1
    (Finset.min'_mem (nonLargeSteps S epsilon)
      ((nonLargeSteps_nonempty_iff S epsilon).2 not_all_large))

theorem firstNonLargeStep_isLong
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (not_all_large : Not (S.AllStepsLarge epsilon)) :
    S.IsLong epsilon (firstNonLargeStep S epsilon not_all_large) := by
  exact le_of_not_ge
    (firstNonLargeStep_not_large S epsilon not_all_large)

theorem firstNonLargeStep_minimal
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (m : Fin depth) (not_large : Not (S.IsLarge epsilon m)) :
    firstNonLargeStep S epsilon not_all_large <= m := by
  exact Finset.min'_le (nonLargeSteps S epsilon) m
    ((mem_nonLargeSteps S epsilon m).2 not_large)

/-! ## Local node checks and exact global finite search -/

variable {A : ActualIntervalCovers S}
  {R : IntervalRootedRefinementScaleTree S}

structure VerifiedStepNodeLowerBounds
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (m : Fin depth) : Prop where
  checked : forall i : Fin (R.tree.levelCount m),
    splitThreshold S eta stage m (R.tree.scale m i) <=
      A.coarseValueAt m (R.tree.scale m i)

namespace VerifiedStepNodeLowerBounds

theorem of_tree
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R)
    (m : Fin depth) (not_large : Not (S.IsLarge epsilon m)) :
    VerifiedStepNodeLowerBounds
      (eta := eta) (stage := stage) A R m where
  checked := V.checked m not_large

end VerifiedStepNodeLowerBounds

theorem verifiedTreeNodeLowerBounds_iff_stepwise :
    VerifiedTreeNodeLowerBounds
        (epsilon := epsilon) (eta := eta) (stage := stage) A R ↔
      forall m, Not (S.IsLarge epsilon m) ->
        VerifiedStepNodeLowerBounds
          (eta := eta) (stage := stage) A R m := by
  constructor
  · intro V m not_large
    exact FamilyStickyScaleChainDividingFiniteNodeProducerV1.VerifiedStepNodeLowerBounds.of_tree V m not_large
  · intro H
    exact ⟨fun m not_large => (H m not_large).checked⟩

theorem verifiedTreeNodeLowerBounds_of_uniqueNonLargeStep
    (m : Fin depth)
    (unique : forall n, Not (S.IsLarge epsilon n) -> n = m)
    (V : VerifiedStepNodeLowerBounds
      (eta := eta) (stage := stage) A R m) :
    VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R where
  checked := by
    intro n not_large i
    have hnm : n = m := unique n not_large
    subst n
    exact V.checked i

theorem verifiedTreeNodeLowerBounds_of_firstNonLarge_unique
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (unique : forall n, Not (S.IsLarge epsilon n) ->
      n = firstNonLargeStep S epsilon not_all_large)
    (V : VerifiedStepNodeLowerBounds
      (eta := eta) (stage := stage) A R
        (firstNonLargeStep S epsilon not_all_large)) :
    VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R :=
  verifiedTreeNodeLowerBounds_of_uniqueNonLargeStep
    (firstNonLargeStep S epsilon not_all_large) unique V

structure FailedTreeNode
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S) where
  step : Fin depth
  step_not_large : Not (S.IsLarge epsilon step)
  node : Fin (R.tree.levelCount step)
  failed : A.coarseValueAt step (R.tree.scale step node) <
    splitThreshold S eta stage step (R.tree.scale step node)

theorem verifiedTreeNodeLowerBounds_or_failedTreeNode :
    VerifiedTreeNodeLowerBounds
        (epsilon := epsilon) (eta := eta) (stage := stage) A R ∨
      Nonempty (FailedTreeNode
        (epsilon := epsilon) (eta := eta) (stage := stage) A R) := by
  classical
  by_cases hV : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R
  · exact Or.inl hV
  · right
    have hchecked : Not (forall m, Not (S.IsLarge epsilon m) ->
        forall i : Fin (R.tree.levelCount m),
          splitThreshold S eta stage m (R.tree.scale m i) <=
            A.coarseValueAt m (R.tree.scale m i)) := by
      intro checked
      exact hV ⟨checked⟩
    push Not at hchecked
    obtain ⟨m, not_large, i, failed⟩ := hchecked
    exact ⟨⟨m, not_large, i, failed⟩⟩

theorem not_verifiedTreeNodeLowerBounds_iff_failedTreeNode :
    Not (VerifiedTreeNodeLowerBounds
        (epsilon := epsilon) (eta := eta) (stage := stage) A R) ↔
      Nonempty (FailedTreeNode
        (epsilon := epsilon) (eta := eta) (stage := stage) A R) := by
  constructor
  · intro hV
    exact (verifiedTreeNodeLowerBounds_or_failedTreeNode
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (A := A) (R := R)).resolve_left hV
  · rintro ⟨F⟩ V
    exact (not_lt_of_ge
      (V.checked F.step F.step_not_large F.node)) F.failed

noncomputable def finiteNodeSearch :
    PLift (VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R) ⊕
      FailedTreeNode
        (epsilon := epsilon) (eta := eta) (stage := stage) A R := by
  classical
  by_cases verified : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R
  · exact Sum.inl ⟨verified⟩
  · exact Sum.inr (Classical.choice
      ((not_verifiedTreeNodeLowerBounds_iff_failedTreeNode
        (epsilon := epsilon) (eta := eta) (stage := stage)
        (A := A) (R := R)).1 verified))

theorem verifiedFirstNonLargeStep_or_failedNode
    (not_all_large : Not (S.AllStepsLarge epsilon)) :
    VerifiedStepNodeLowerBounds
        (eta := eta) (stage := stage) A R
          (firstNonLargeStep S epsilon not_all_large) ∨
      exists i : Fin
          (R.tree.levelCount
            (firstNonLargeStep S epsilon not_all_large)),
        A.coarseValueAt
            (firstNonLargeStep S epsilon not_all_large)
            (R.tree.scale (firstNonLargeStep S epsilon not_all_large) i) <
          splitThreshold S eta stage
            (firstNonLargeStep S epsilon not_all_large)
            (R.tree.scale (firstNonLargeStep S epsilon not_all_large) i) := by
  classical
  by_cases hV : VerifiedStepNodeLowerBounds
      (eta := eta) (stage := stage) A R
        (firstNonLargeStep S epsilon not_all_large)
  · exact Or.inl hV
  · right
    have hchecked : Not (forall i : Fin
        (R.tree.levelCount (firstNonLargeStep S epsilon not_all_large)),
      splitThreshold S eta stage
          (firstNonLargeStep S epsilon not_all_large)
          (R.tree.scale (firstNonLargeStep S epsilon not_all_large) i) <=
        A.coarseValueAt
          (firstNonLargeStep S epsilon not_all_large)
          (R.tree.scale (firstNonLargeStep S epsilon not_all_large) i)) := by
      intro checked
      exact hV ⟨checked⟩
    push Not at hchecked
    exact hchecked

theorem no_verifiedTreeNodeLowerBounds_of_firstNonLarge_failedNode
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (i : Fin (R.tree.levelCount
      (firstNonLargeStep S epsilon not_all_large)))
    (failed :
      A.coarseValueAt
          (firstNonLargeStep S epsilon not_all_large)
          (R.tree.scale (firstNonLargeStep S epsilon not_all_large) i) <
        splitThreshold S eta stage
          (firstNonLargeStep S epsilon not_all_large)
          (R.tree.scale (firstNonLargeStep S epsilon not_all_large) i)) :
    Not (VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage) A R) := by
  intro V
  exact (not_lt_of_ge
    (V.checked (firstNonLargeStep S epsilon not_all_large)
      (firstNonLargeStep_not_large S epsilon not_all_large) i)) failed

/-! ## Local checks directly produce the dividing witness -/

namespace VerifiedStepNodeLowerBounds

variable {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {m : Fin depth}

theorem actual_buffered_lower_with_constant
    (V : VerifiedStepNodeLowerBounds
      (eta := eta) (stage := stage) (C.toActualIntervalCovers S) R m)
    (tau_pos : forall n, 0 < S.tau n)
    (hTwoEta : (2 : Real) <= eta stage)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (rho : NNReal) (buffered : S.IsBuffered epsilon m rho) :
    splitThreshold S eta stage m rho <=
      actualStrictLocalizationConstant iota *
        (C.toActualIntervalCovers S).coarseValueAt m rho := by
  have eta_nonneg : (0 : Real) <= eta stage :=
    (by norm_num : (0 : Real) <= 2).trans hTwoEta
  have epsilon_nonneg : (0 : Real) <= epsilon :=
    eta_nonneg.trans eta_stage_le_epsilon
  let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
  have hsigma := R.located_scale_mem_interval
    epsilon_nonneg m rho buffered
  have sigma_pos : 0 < sigma := (R.tau_pos m).trans_le hsigma.1
  have rho_pos : 0 < rho := sigma_pos.trans_le hsigma.2
  let L : StrictConstantLocatedCoarseValueLocalization
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R
        (actualStrictLocalizationConstant iota) :=
    FamilyStickyScaleChainActualStrictLossWithConstantV1.CoherentIntervalLocalizationGeometry.toActualStrictConstantLocatedCoarseValueLocalization
      (C := C) (R := R) tau_pos hTwoEta eta_stage_le_epsilon
  rcases lt_or_eq_of_le hsigma.2 with strict | equal
  · exact splitThreshold_le_constant_mul_of_located_coarseValue
      (C.toActualIntervalCovers S) m sigma rho sigma_pos rho_pos
      eta_nonneg (actualStrictLocalizationConstant iota)
      (V.checked (R.tree.locate m rho))
      (L.localized_le m rho buffered strict)
  · have sigma_eq : sigma = rho := by
      simpa [sigma] using equal
    rw [← sigma_eq]
    calc
      splitThreshold S eta stage m sigma <=
          (C.toActualIntervalCovers S).coarseValueAt m sigma :=
        V.checked (R.tree.locate m rho)
      _ = 1 * (C.toActualIntervalCovers S).coarseValueAt m sigma := by
        simp
      _ <= actualStrictLocalizationConstant iota *
          (C.toActualIntervalCovers S).coarseValueAt m sigma :=
        mul_le_mul' (one_le_actualStrictLocalizationConstant iota) le_rfl

end VerifiedStepNodeLowerBounds

variable {outerDepth chainDepth adjacentDepth N : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {profile : Nat -> Real}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

noncomputable def constantWitnessAtNonLargeStep_of_localNodes
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily
      S (C.toActualIntervalCovers S) adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (profile_stage_le_epsilon : profile stage <= epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage profile)
    (adjacentExponent :
      AdjacentBufferedHierarchyFamily.ExponentBudgetData G stage profile)
    (m : Fin outerDepth) (not_large : Not (S.IsLarge epsilon m))
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
      ((B.productBudget_of_actual
        (fun n => (S.theta n : ENNReal) ^ (-profile (stage - 1)))
        (globalExponent.actualProductBudget B)) m)
  adjacent_upper := adjacentExponent.adjacent_upper G m
  middle_lower_with_constant := by
    intro rho lower upper
    exact V.actual_buffered_lower_with_constant
      (fun n => delta_pos.trans_le (S.delta_le_tau n))
      two_le_profile profile_stage_le_epsilon rho ⟨lower, upper⟩

noncomputable def constantWitnessAtFirstNonLargeStep_of_localNodes
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily
      S (C.toActualIntervalCovers S) adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (profile_stage_le_epsilon : profile stage <= epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage profile)
    (adjacentExponent :
      AdjacentBufferedHierarchyFamily.ExponentBudgetData G stage profile)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (V : VerifiedStepNodeLowerBounds
      (eta := profile) (stage := stage)
      (C.toActualIntervalCovers S) R
        (firstNonLargeStep S epsilon not_all_large))
    (two_le_profile : (2 : Real) <= profile stage)
    (delta_pos : 0 < delta) :
    KatzTaoConstantDividingWitness delta N epsilon profile
      (actualStrictLocalizationConstant iota) :=
  constantWitnessAtNonLargeStep_of_localNodes
    C R B G stage stage_pos stage_le profile_stage_le_epsilon
      globalExponent adjacentExponent
      (firstNonLargeStep S epsilon not_all_large)
      (firstNonLargeStep_not_large S epsilon not_all_large)
      V two_le_profile delta_pos

variable {eta : Nat -> Real}

theorem exists_recoveredLiteralWitness_of_firstNonLargeLocalNodes
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily
      S (C.toActualIntervalCovers S) adjacentDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (globalAllocation : GlobalExponentAllocation B S (oneBasedStage slot)
      (reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)))
    (adjacentAllocation : AdjacentExponentAllocation G (oneBasedStage slot)
      (reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)))
    (not_all_large : Not (S.AllStepsLarge epsilon))
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
  have room : eta (oneBasedStage slot) + loss <= epsilon := by
    exact eta_add_halfReservedExponentRoom_le strict_room
  have reserved_stage_le :
      reservedProfile (oneBasedStage slot) <= epsilon := by
    exact reserveTailLoss_stage_le room
  have two_le_reserved :
      (2 : Real) <= reservedProfile (oneBasedStage slot) := by
    have h := two_le_add_halfReservedExponentRoom_of_two_le_zero
      eta_monotone two_le_zero strict_room
    simpa [reservedProfile, loss] using h
  let W : KatzTaoConstantDividingWitness delta N epsilon reservedProfile
      (actualStrictLocalizationConstant iota) :=
    constantWitnessAtFirstNonLargeStep_of_localNodes
      C R B G (oneBasedStage slot) (oneBasedStage_pos slot)
        (oneBasedStage_le slot) reserved_stage_le
        (globalAllocation.toExponentBudgetData delta_pos)
        (adjacentAllocation.toExponentBudgetData delta_pos)
        not_all_large V two_le_reserved delta_pos
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

#print axioms mem_nonLargeSteps
#print axioms nonLargeSteps_nonempty_iff
#print axioms firstNonLargeStep_not_large
#print axioms firstNonLargeStep_isLong
#print axioms firstNonLargeStep_minimal
#print axioms verifiedTreeNodeLowerBounds_iff_stepwise
#print axioms verifiedTreeNodeLowerBounds_of_firstNonLarge_unique
#print axioms verifiedTreeNodeLowerBounds_or_failedTreeNode
#print axioms not_verifiedTreeNodeLowerBounds_iff_failedTreeNode
#print axioms finiteNodeSearch
#print axioms verifiedFirstNonLargeStep_or_failedNode
#print axioms no_verifiedTreeNodeLowerBounds_of_firstNonLarge_failedNode
#print axioms VerifiedStepNodeLowerBounds.actual_buffered_lower_with_constant
#print axioms constantWitnessAtNonLargeStep_of_localNodes
#print axioms constantWitnessAtFirstNonLargeStep_of_localNodes
#print axioms exists_recoveredLiteralWitness_of_firstNonLargeLocalNodes

end
end FamilyStickyScaleChainDividingFiniteNodeProducerV1
