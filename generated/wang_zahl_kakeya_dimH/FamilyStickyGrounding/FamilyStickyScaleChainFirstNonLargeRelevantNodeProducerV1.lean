import FamilyStickyGrounding.FamilyStickyScaleChainActualUnitCapProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1

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
open FamilyStickyFiniteFamilyMaximalConcentrationV1

noncomputable section

/-!
# Relevant-node producer at the first non-large interval

The old local certificate checks every node of an arbitrary rooted tree.
Only nodes below the upper buffered cutoff can ever be returned by `locate`
on a buffered scale.  This module restricts the finite checks to exactly that
necessary range, realizes them from literal contained-mass selections, and
returns the first actual failure when a check does not close.

A failed relevant node has a useful exact alternative.  It is either itself
an actual buffered bad scale, or it lies strictly below the lower buffered
cutoff while still carrying the literal coarse-value deficit.  Thus the
failure branch records more than the negation of a certificate.
-/

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {profile : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}

/-! ## The exact finite range that can serve as a located node -/

def bufferedLowerCutoff
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (m : Fin depth) : ENNReal :=
  (S.tau m : ENNReal) *
    (((S.theta m / S.tau m : NNReal) : ENNReal) ^ epsilon)

def bufferedUpperCutoff
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (m : Fin depth) : ENNReal :=
  (S.theta m : ENNReal) *
    (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon)

theorem isBuffered_iff_cutoffs
    (m : Fin depth) (rho : NNReal) :
    S.IsBuffered epsilon m rho <->
      bufferedLowerCutoff S epsilon m <= (rho : ENNReal) ∧
        (rho : ENNReal) <= bufferedUpperCutoff S epsilon m := by
  rfl

/-- A node is relevant precisely when it lies below the upper endpoint of
the buffered core.  Every node has the lower interval bound automatically
from the rooted-tree fields. -/
def IsRelevantTreeNode
    (R : IntervalRootedRefinementScaleTree S)
    (m : Fin depth) (i : Fin (R.tree.levelCount m)) : Prop :=
  (R.tree.scale m i : ENNReal) <= bufferedUpperCutoff S epsilon m

theorem bufferedUpperCutoff_le_theta
    (epsilon_nonneg : 0 <= epsilon) (m : Fin depth) :
    bufferedUpperCutoff S epsilon m <= (S.theta m : ENNReal) := by
  have ratio_nn : S.tau m / S.theta m <= 1 :=
    div_le_one_of_le₀ (S.tau_le_theta m) bot_le
  have ratio :
      (((S.tau m / S.theta m : NNReal) : ENNReal)) <= 1 := by
    exact_mod_cast ratio_nn
  have power_le_one :
      (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon) <= 1 :=
    ENNReal.rpow_le_one ratio epsilon_nonneg
  unfold bufferedUpperCutoff
  calc
    (S.theta m : ENNReal) *
        (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon) <=
      (S.theta m : ENNReal) * 1 := by gcongr
    _ = (S.theta m : ENNReal) := by simp

theorem relevantNode_scale_le_theta
    (R : IntervalRootedRefinementScaleTree S)
    (epsilon_nonneg : 0 <= epsilon) (m : Fin depth)
    (i : Fin (R.tree.levelCount m))
    (relevant : IsRelevantTreeNode
      (epsilon := epsilon) R m i) :
    R.tree.scale m i <= S.theta m := by
  exact ENNReal.coe_le_coe.mp
    (relevant.trans (bufferedUpperCutoff_le_theta epsilon_nonneg m))

theorem relevantNode_scale_le_one
    (R : IntervalRootedRefinementScaleTree S)
    (epsilon_nonneg : 0 <= epsilon) (m : Fin depth)
    (i : Fin (R.tree.levelCount m))
    (relevant : IsRelevantTreeNode
      (epsilon := epsilon) R m i) :
    R.tree.scale m i <= 1 :=
  (relevantNode_scale_le_theta R epsilon_nonneg m i relevant).trans
    (S.theta_le_one m)

theorem locatedNode_isRelevant
    (R : IntervalRootedRefinementScaleTree S)
    (epsilon_nonneg : 0 <= epsilon) (m : Fin depth)
    (rho : NNReal) (buffered : S.IsBuffered epsilon m rho) :
    IsRelevantTreeNode (epsilon := epsilon) R m
      (R.tree.locate m rho) := by
  have located := R.located_scale_mem_interval
    epsilon_nonneg m rho buffered
  calc
    (R.tree.scale m (R.tree.locate m rho) : ENNReal) <=
        (rho : ENNReal) := by exact_mod_cast located.2
    _ <= bufferedUpperCutoff S epsilon m := buffered.2

/-! ## Literal mass selections produce the required node checks -/

variable {A : ActualIntervalCovers S}
  {R : IntervalRootedRefinementScaleTree S} {m : Fin depth}

/-- The literal actual cover evaluated at a relevant tree node. -/
def actualRelevantTreeNodeCover
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (epsilon_nonneg : 0 <= epsilon)
    (m : Fin depth) (i : Fin (R.tree.levelCount m))
    (relevant : IsRelevantTreeNode (epsilon := epsilon) R m i) :
    StickyScaleCover (A.fine m) (R.tree.scale m i) :=
  (A.multiscale m).cover (R.tree.scale m i)
    (R.tau_le_scale m i)
    (relevantNode_scale_le_one R epsilon_nonneg m i relevant)

theorem coarseValueAt_treeNode_eq
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (epsilon_nonneg : 0 <= epsilon)
    (m : Fin depth) (i : Fin (R.tree.levelCount m))
    (relevant : IsRelevantTreeNode (epsilon := epsilon) R m i) :
    A.coarseValueAt m (R.tree.scale m i) =
      StickyScaleCover.coarseDeltaMax
        (actualRelevantTreeNodeCover A R epsilon_nonneg m i relevant) := by
  exact A.coarseValueAt_eq m (R.tree.scale m i)
    (R.tau_le_scale m i)
    (relevantNode_scale_le_one R epsilon_nonneg m i relevant)

/-- The weakest source-shaped selection input used here: for every relevant
node, choose a positive-volume convex test body whose literal contained mass
dominates the cross-multiplied splitting threshold. -/
structure RelevantNodeMassSelections
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (epsilon_nonneg : 0 <= epsilon)
    (m : Fin depth) where
  testBody : forall i : Fin (R.tree.levelCount m),
    IsRelevantTreeNode (epsilon := epsilon) R m i -> ConvexBody Space
  bodyVolume_ne_zero : forall i relevant,
    volume (testBody i relevant : Set Space) ≠ 0
  containedMass_lower : forall i relevant,
    splitThreshold S profile stage m (R.tree.scale m i) *
        volume (testBody i relevant : Set Space) <=
      containedMass
        (actualRelevantTreeNodeCover A R epsilon_nonneg m i relevant).activeCoarseFamily
        (testBody i relevant)

/-- Only relevant nodes are required by the constant-bearing stopping
endpoint. -/
structure VerifiedRelevantStepNodeLowerBounds
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (m : Fin depth) : Prop where
  checked : forall i : Fin (R.tree.levelCount m),
    IsRelevantTreeNode (epsilon := epsilon) R m i ->
      splitThreshold S profile stage m (R.tree.scale m i) <=
        A.coarseValueAt m (R.tree.scale m i)

theorem VerifiedRelevantStepNodeLowerBounds.of_full
    (V : VerifiedStepNodeLowerBounds
      (eta := profile) (stage := stage) A R m) :
    VerifiedRelevantStepNodeLowerBounds
      (epsilon := epsilon) (profile := profile) (stage := stage) A R m where
  checked := fun i _ => V.checked i

theorem RelevantNodeMassSelections.toVerifiedRelevantStepNodeLowerBounds
    (epsilon_nonneg : 0 <= epsilon)
    (D : RelevantNodeMassSelections
      (epsilon := epsilon) (profile := profile) (stage := stage)
      A R epsilon_nonneg m) :
    VerifiedRelevantStepNodeLowerBounds
      (epsilon := epsilon) (profile := profile) (stage := stage) A R m where
  checked := by
    intro i relevant
    let Q := actualRelevantTreeNodeCover A R epsilon_nonneg m i relevant
    let K := D.testBody i relevant
    have concentration_lower :
        splitThreshold S profile stage m (R.tree.scale m i) <=
          concentration Q.activeCoarseFamily K := by
      rw [concentration_eq_containedMass_div]
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl (D.bodyVolume_ne_zero i relevant))
        (Or.inl K.isCompact.measure_lt_top.ne)).2
      exact D.containedMass_lower i relevant
    rw [coarseValueAt_treeNode_eq A R epsilon_nonneg m i relevant]
    exact concentration_lower.trans
      (concentration_le_maximalConcentration Q.activeCoarseFamily K)

/-! ## Exact actual obstruction from an empty node family -/

theorem coarseDeltaMax_eq_zero_of_activeCoarse_eq_empty
    {rho : NNReal} {index : Type*} [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (Q : StickyScaleCover fine rho) (empty : Q.activeCoarse = ∅) :
    StickyScaleCover.coarseDeltaMax Q = 0 := by
  apply le_antisymm
  · unfold StickyScaleCover.coarseDeltaMax
    calc
      maximalConcentration Q.activeCoarseFamily <=
          (Fintype.card {k // k ∈ Q.activeCoarse} : ENNReal) :=
        maximalConcentration_le_card Q.activeCoarseFamily
      _ = 0 := by simp [empty]
  · exact bot_le

theorem splitThreshold_treeNode_pos
    (R : IntervalRootedRefinementScaleTree S)
    (epsilon_nonneg : 0 <= epsilon)
    (m : Fin depth) (i : Fin (R.tree.levelCount m))
    (relevant : IsRelevantTreeNode (epsilon := epsilon) R m i) :
    0 < splitThreshold S profile stage m (R.tree.scale m i) := by
  have scale_pos : 0 < R.tree.scale m i :=
    (R.tau_pos m).trans_le (R.tau_le_scale m i)
  have theta_pos : 0 < S.theta m :=
    scale_pos.trans_le
      (relevantNode_scale_le_theta R epsilon_nonneg m i relevant)
  unfold splitThreshold
  exact ENNReal.rpow_pos
    (ENNReal.coe_pos.mpr (div_pos theta_pos scale_pos)) ENNReal.coe_ne_top

/-- Empty active coarse data at a legal relevant node gives a literal strict
failure, so the existing actual-cover fields alone cannot generate the node
certificate. -/
theorem node_failure_of_activeCoarse_eq_empty
    (epsilon_nonneg : 0 <= epsilon)
    (m : Fin depth) (i : Fin (R.tree.levelCount m))
    (relevant : IsRelevantTreeNode (epsilon := epsilon) R m i)
    (empty :
      (actualRelevantTreeNodeCover A R epsilon_nonneg m i relevant).activeCoarse = ∅) :
    A.coarseValueAt m (R.tree.scale m i) <
      splitThreshold S profile stage m (R.tree.scale m i) := by
  rw [coarseValueAt_treeNode_eq A R epsilon_nonneg m i relevant,
    coarseDeltaMax_eq_zero_of_activeCoarse_eq_empty _ empty]
  exact splitThreshold_treeNode_pos R epsilon_nonneg m i relevant

/-! ## Finite first-failure search -/

def relevantTreeNodes
    (R : IntervalRootedRefinementScaleTree S) (m : Fin depth) :
    Finset (Fin (R.tree.levelCount m)) := by
  classical
  exact Finset.univ.filter fun i =>
    IsRelevantTreeNode (epsilon := epsilon) R m i

@[simp] theorem mem_relevantTreeNodes
    (R : IntervalRootedRefinementScaleTree S) (m : Fin depth)
    (i : Fin (R.tree.levelCount m)) :
    i ∈ relevantTreeNodes (epsilon := epsilon) R m <->
      IsRelevantTreeNode (epsilon := epsilon) R m i := by
  classical
  simp [relevantTreeNodes]

def failedRelevantTreeNodes
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S) (m : Fin depth) :
    Finset (Fin (R.tree.levelCount m)) := by
  classical
  exact (relevantTreeNodes (epsilon := epsilon) R m).filter fun i =>
    A.coarseValueAt m (R.tree.scale m i) <
      splitThreshold S profile stage m (R.tree.scale m i)

@[simp] theorem mem_failedRelevantTreeNodes
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S) (m : Fin depth)
    (i : Fin (R.tree.levelCount m)) :
    i ∈ failedRelevantTreeNodes
        (epsilon := epsilon) (profile := profile) (stage := stage) A R m <->
      IsRelevantTreeNode (epsilon := epsilon) R m i ∧
        A.coarseValueAt m (R.tree.scale m i) <
          splitThreshold S profile stage m (R.tree.scale m i) := by
  classical
  simp [failedRelevantTreeNodes]

/-- The first failed relevant node, retaining every earlier successful
relevant check. -/
structure FirstRelevantNodeFailure
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (m : Fin depth) where
  node : Fin (R.tree.levelCount m)
  relevant : IsRelevantTreeNode (epsilon := epsilon) R m node
  failed : A.coarseValueAt m (R.tree.scale m node) <
    splitThreshold S profile stage m (R.tree.scale m node)
  earlier_checked : forall j : Fin (R.tree.levelCount m), j < node ->
    IsRelevantTreeNode (epsilon := epsilon) R m j ->
      splitThreshold S profile stage m (R.tree.scale m j) <=
        A.coarseValueAt m (R.tree.scale m j)

/-- Proof-relevant finite search at one actual interval. -/
noncomputable def relevantNodeSearch
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S) (m : Fin depth) :
    PLift (VerifiedRelevantStepNodeLowerBounds
      (epsilon := epsilon) (profile := profile) (stage := stage) A R m) ⊕
      FirstRelevantNodeFailure
        (epsilon := epsilon) (profile := profile) (stage := stage) A R m := by
  classical
  let failures := failedRelevantTreeNodes
    (epsilon := epsilon) (profile := profile) (stage := stage) A R m
  by_cases nonempty : failures.Nonempty
  · right
    let first := failures.min' nonempty
    have first_mem : first ∈ failures := Finset.min'_mem failures nonempty
    have first_spec := (mem_failedRelevantTreeNodes
      (epsilon := epsilon) (profile := profile) (stage := stage)
      A R m first).1 first_mem
    refine ⟨first, first_spec.1, first_spec.2, ?_⟩
    intro j earlier relevant
    by_contra not_checked
    have failed : A.coarseValueAt m (R.tree.scale m j) <
        splitThreshold S profile stage m (R.tree.scale m j) :=
      lt_of_not_ge not_checked
    have member : j ∈ failures := by
      exact (mem_failedRelevantTreeNodes
        (epsilon := epsilon) (profile := profile) (stage := stage)
        A R m j).2 ⟨relevant, failed⟩
    exact (not_le_of_gt earlier) (Finset.min'_le failures j member)
  · left
    refine ⟨⟨?_⟩⟩
    intro i relevant
    by_contra not_checked
    have failed : A.coarseValueAt m (R.tree.scale m i) <
        splitThreshold S profile stage m (R.tree.scale m i) :=
      lt_of_not_ge not_checked
    apply nonempty
    exact ⟨i, (mem_failedRelevantTreeNodes
      (epsilon := epsilon) (profile := profile) (stage := stage)
      A R m i).2 ⟨relevant, failed⟩⟩

/-- The failure is either a genuine buffered strict split, or a precise
below-core concentration deficit. -/
theorem FirstRelevantNodeFailure.actualBadScale_or_belowLowerCutoff
    (F : FirstRelevantNodeFailure
      (epsilon := epsilon) (profile := profile) (stage := stage) A R m) :
    IsBadScale A epsilon profile stage m (R.tree.scale m F.node) ∨
      (R.tree.scale m F.node : ENNReal) <
          bufferedLowerCutoff S epsilon m ∧
        A.coarseValueAt m (R.tree.scale m F.node) <
          splitThreshold S profile stage m (R.tree.scale m F.node) := by
  by_cases lower : bufferedLowerCutoff S epsilon m <=
      (R.tree.scale m F.node : ENNReal)
  · exact Or.inl ⟨⟨lower, F.relevant⟩, F.failed⟩
  · exact Or.inr ⟨lt_of_not_ge lower, F.failed⟩

/-! ## The weakened finite certificate still gives the actual lower bound -/

namespace VerifiedRelevantStepNodeLowerBounds

variable {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {m : Fin depth}

theorem actual_buffered_lower_with_constant
    (V : VerifiedRelevantStepNodeLowerBounds
      (epsilon := epsilon) (profile := profile) (stage := stage)
      (C.toActualIntervalCovers S) R m)
    (tau_pos : forall n, 0 < S.tau n)
    (two_le_profile : (2 : Real) <= profile stage)
    (profile_stage_le_epsilon : profile stage <= epsilon)
    (rho : NNReal) (buffered : S.IsBuffered epsilon m rho) :
    splitThreshold S profile stage m rho <=
      actualStrictLocalizationConstant iota *
        (C.toActualIntervalCovers S).coarseValueAt m rho := by
  have profile_nonneg : (0 : Real) <= profile stage :=
    (by norm_num : (0 : Real) <= 2).trans two_le_profile
  have epsilon_nonneg : (0 : Real) <= epsilon :=
    profile_nonneg.trans profile_stage_le_epsilon
  let sigma : NNReal := R.tree.scale m (R.tree.locate m rho)
  have hsigma := R.located_scale_mem_interval
    epsilon_nonneg m rho buffered
  have sigma_pos : 0 < sigma := (R.tau_pos m).trans_le hsigma.1
  have rho_pos : 0 < rho := sigma_pos.trans_le hsigma.2
  have node_checked : splitThreshold S profile stage m sigma <=
      (C.toActualIntervalCovers S).coarseValueAt m sigma :=
    V.checked (R.tree.locate m rho)
      (locatedNode_isRelevant R epsilon_nonneg m rho buffered)
  let L : StrictConstantLocatedCoarseValueLocalization
      (epsilon := epsilon) (eta := profile) (stage := stage)
      (C.toActualIntervalCovers S) R
        (actualStrictLocalizationConstant iota) :=
    FamilyStickyScaleChainActualStrictLossWithConstantV1.CoherentIntervalLocalizationGeometry.toActualStrictConstantLocatedCoarseValueLocalization
      (C := C) (R := R) tau_pos two_le_profile profile_stage_le_epsilon
  rcases lt_or_eq_of_le hsigma.2 with strict | equal
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
/-! ## Recovered endpoint using only relevant-node checks -/

variable {outerDepth chainDepth N : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The direct constant-bearing witness with the weakened relevant-node
certificate. -/
noncomputable def constantWitnessAtNonLargeStep_of_relevantNodes
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (profile_stage_le_epsilon : profile stage <= epsilon)
    (m : Fin outerDepth) (not_large : Not (S.IsLarge epsilon m))
    (budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S) profile stage m)
    (V : VerifiedRelevantStepNodeLowerBounds
      (epsilon := epsilon) (profile := profile) (stage := stage)
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

/-- Small-delta recovery now consumes only the relevant finite node checks at
the computed first non-large interval. -/
theorem exists_recoveredLiteralWitness_of_relevantSelectedNumericalBudgets
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
    constantWitnessAtNonLargeStep_of_relevantNodes
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

/-- Both actual unit-cap producers and the weakened node certificate close
the recovered endpoint. -/
theorem exists_recoveredLiteralWitness_of_actualUnitCaps_and_relevantNodes
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalCaps : ActualGlobalFactorCaps B
      (firstNonLargeStep S epsilon not_all_large))
    (active_card_le_one :
      (actualAdjacentScaleCover (C.toActualIntervalCovers S)
        (firstNonLargeStep S epsilon not_all_large)).activeCoarse.card <= 1)
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
  have pred_nonneg :
      0 <= reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)
        (oneBasedStage slot - 1) :=
    reserveTailLoss_pred_nonneg (oneBasedStage_pos slot)
      eta_monotone two_le_zero
  have budgets := selectedNumericalBudgets_of_unitCaps
    B (C.toActualIntervalCovers S)
      (firstNonLargeStep S epsilon not_all_large)
      pred_nonneg delta_pos
      (actualGlobalProductAt_le_one_of_factorCaps B
        (firstNonLargeStep S epsilon not_all_large) globalCaps)
      (adjacentCoarseValue_le_one_of_activeCoarse_card_le_one
        (C.toActualIntervalCovers S)
        (firstNonLargeStep S epsilon not_all_large) active_card_le_one)
  exact exists_recoveredLiteralWitness_of_relevantSelectedNumericalBudgets
    C R B slot eta_monotone two_le_zero strict_room not_all_large
      budgets V delta_pos delta_le

/-- Literal mass selections remove the relevant-node certificate argument. -/
theorem exists_recoveredLiteralWitness_of_actualUnitCaps_and_nodeMassSelections
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalCaps : ActualGlobalFactorCaps B
      (firstNonLargeStep S epsilon not_all_large))
    (active_card_le_one :
      (actualAdjacentScaleCover (C.toActualIntervalCovers S)
        (firstNonLargeStep S epsilon not_all_large)).activeCoarse.card <= 1)
    (epsilon_nonneg : 0 <= epsilon)
    (M : RelevantNodeMassSelections
      (epsilon := epsilon)
      (profile := reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (stage := oneBasedStage slot)
      (C.toActualIntervalCovers S) R epsilon_nonneg
        (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))) := by
  exact exists_recoveredLiteralWitness_of_actualUnitCaps_and_relevantNodes
    C R B slot eta_monotone two_le_zero strict_room not_all_large
      globalCaps active_card_le_one
      (M.toVerifiedRelevantStepNodeLowerBounds epsilon_nonneg)
      delta_pos delta_le

/-! ## Search output with an analytic failure branch -/

inductive FirstRelevantNodeAnalyticAlternative
    (A : ActualIntervalCovers S)
    (R : IntervalRootedRefinementScaleTree S)
    (m : Fin outerDepth) where
  | actualBad
      (failure : FirstRelevantNodeFailure
        (epsilon := epsilon) (profile := profile) (stage := stage) A R m)
      (bad : IsBadScale A epsilon profile stage m
        (R.tree.scale m failure.node))
  | belowLowerCutoff
      (failure : FirstRelevantNodeFailure
        (epsilon := epsilon) (profile := profile) (stage := stage) A R m)
      (below : (R.tree.scale m failure.node : ENNReal) <
        bufferedLowerCutoff S epsilon m)

noncomputable def FirstRelevantNodeFailure.toAnalyticAlternative
    {A : ActualIntervalCovers S}
    {R : IntervalRootedRefinementScaleTree S}
    {m : Fin outerDepth}
    (F : FirstRelevantNodeFailure
      (epsilon := epsilon) (profile := profile) (stage := stage) A R m) :
    FirstRelevantNodeAnalyticAlternative
      (epsilon := epsilon) (profile := profile) (stage := stage) A R m := by
  by_cases lower : bufferedLowerCutoff S epsilon m <=
      (R.tree.scale m F.node : ENNReal)
  · exact .actualBad F ⟨⟨lower, F.relevant⟩, F.failed⟩
  · exact .belowLowerCutoff F (lt_of_not_ge lower)

/-- The requested two-branch actual search: success is the recovered literal
witness; failure is the first relevant deficit, classified as a genuine
buffered split or a below-core boundary deficit. -/
noncomputable def recoveredLiteralWitnessOrFirstRelevantNodeAlternative
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalCaps : ActualGlobalFactorCaps B
      (firstNonLargeStep S epsilon not_all_large))
    (active_card_le_one :
      (actualAdjacentScaleCover (C.toActualIntervalCovers S)
        (firstNonLargeStep S epsilon not_all_large)).activeCoarse.card <= 1)
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
          (firstNonLargeStep S epsilon not_all_large) := by
  let m := firstNonLargeStep S epsilon not_all_large
  let selected := relevantNodeSearch
    (epsilon := epsilon)
    (profile := reserveTailLoss eta (oneBasedStage slot)
      (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
    (stage := oneBasedStage slot) (C.toActualIntervalCovers S) R m
  cases selected with
  | inl verified =>
      exact Sum.inl ⟨
        (exists_recoveredLiteralWitness_of_actualUnitCaps_and_relevantNodes
          C R B slot eta_monotone two_le_zero strict_room not_all_large
            globalCaps active_card_le_one verified.down delta_pos delta_le)⟩
  | inr failure =>
      exact Sum.inr failure.toAnalyticAlternative

#print axioms constantWitnessAtNonLargeStep_of_relevantNodes
#print axioms exists_recoveredLiteralWitness_of_relevantSelectedNumericalBudgets
#print axioms exists_recoveredLiteralWitness_of_actualUnitCaps_and_relevantNodes
#print axioms exists_recoveredLiteralWitness_of_actualUnitCaps_and_nodeMassSelections
#print axioms FirstRelevantNodeFailure.toAnalyticAlternative
#print axioms recoveredLiteralWitnessOrFirstRelevantNodeAlternative


#print axioms bufferedUpperCutoff_le_theta
#print axioms relevantNode_scale_le_theta
#print axioms locatedNode_isRelevant
#print axioms coarseValueAt_treeNode_eq
#print axioms RelevantNodeMassSelections.toVerifiedRelevantStepNodeLowerBounds
#print axioms coarseDeltaMax_eq_zero_of_activeCoarse_eq_empty
#print axioms node_failure_of_activeCoarse_eq_empty
#print axioms mem_failedRelevantTreeNodes
#print axioms relevantNodeSearch
#print axioms FirstRelevantNodeFailure.actualBadScale_or_belowLowerCutoff
#print axioms VerifiedRelevantStepNodeLowerBounds.actual_buffered_lower_with_constant

end
end FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1
