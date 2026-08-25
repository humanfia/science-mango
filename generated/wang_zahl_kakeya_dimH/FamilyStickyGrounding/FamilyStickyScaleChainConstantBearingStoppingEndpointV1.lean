import FamilyStickyGrounding.FamilyStickyScaleChainActualStrictLossWithConstantV1
import FamilyStickyGrounding.FamilyStickyScaleChainAdjacentUpperProducerV1

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainConstantBearingStoppingEndpointV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesNoSplitV2
open FamilyStickyDividingScalesChainAtEveryAdapterV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainExponentProductBudgetV1
open FamilyStickyScaleChainAdjacentUpperProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1

noncomputable section

/-!
# Constant-bearing finite stopping endpoint

The actual strict localization theorem gives

`splitThreshold rho <= K * middleValue rho`

with an explicit finite-family/dimensional constant `K`.  This module keeps
that constant through the finite stopping choice and the global/adjacent
telescope.  It does not try to turn the result into the stronger
constant-one `KatzTaoDividingWitness`.

The final conversion theorem below records the exact and only additional
inequality needed to recover the old constant-one endpoint: the factor `K`
must be removable from the buffered middle lower bound.  All other endpoint
fields are copied verbatim.
-/

/-! ## Generic constant-bearing finite stopping -/

/-- Katz--Tao stopping data whose buffered lower bound retains an explicit
multiplicative constant.  The global and adjacent bounds are unchanged. -/
structure KatzTaoConstantStoppingRun
    (delta : NNReal) (depth N : Nat) (epsilon : Real)
    (eta : Nat -> Real) (K : ENNReal)
    (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  eta_stage_le_epsilon : eta stage <= epsilon
  globalValue : Fin depth -> ENNReal
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  global_upper : forall m,
    globalValue m <= (S.theta m : ENNReal) ^ (-eta (stage - 1))
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal : forall m, S.IsLarge epsilon m ∨
    forall rho, S.IsBuffered epsilon m rho ->
      (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage) <=
        K * middleValue m rho

/-- Exact output carried by a long terminal Katz--Tao interval when the
strict localization loss is `K`. -/
structure KatzTaoConstantDividingWitness
    (delta : NNReal) (N : Nat) (epsilon : Real)
    (eta : Nat -> Real) (K : ENNReal) where
  tau : NNReal
  theta : NNReal
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  delta_le_tau : delta <= tau
  tau_le_theta : tau <= theta
  theta_le_one : theta <= 1
  long : (tau : ENNReal) <= (delta : ENNReal) ^ epsilon * (theta : ENNReal)
  globalValue : ENNReal
  adjacentValue : ENNReal
  middleValue : NNReal -> ENNReal
  global_upper : globalValue <= (theta : ENNReal) ^ (-eta (stage - 1))
  adjacent_upper : adjacentValue <=
    (((theta / tau : NNReal) : ENNReal) ^ eta (stage - 1))
  middle_lower_with_constant : forall rho : NNReal,
    (tau : ENNReal) *
          (((theta / tau : NNReal) : ENNReal) ^ epsilon) <= rho ->
      (rho : ENNReal) <=
          (theta : ENNReal) *
            (((tau / theta : NNReal) : ENNReal) ^ epsilon) ->
      (((theta / rho : NNReal) : ENNReal) ^ eta stage) <=
        K * middleValue rho

namespace KatzTaoConstantStoppingRun

variable {delta : NNReal} {depth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {K : ENNReal}
  {S : FiniteScaleSequence delta depth}

/-- Finiteness chooses a long interval without changing the explicit
constant in its buffered lower bound. -/
theorem allLarge_or_witness
    (R : KatzTaoConstantStoppingRun delta depth N epsilon eta K S) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoConstantDividingWitness delta N epsilon eta K) := by
  let barrier : Fin depth -> Prop := fun m =>
    forall rho, S.IsBuffered epsilon m rho ->
      (((S.theta m / rho : NNReal) : ENNReal) ^ eta R.stage) <=
        K * R.middleValue m rho
  rcases S.allStepsLarge_or_exists_long epsilon barrier R.terminal with
    hall | ⟨m, hlong, hbarrier⟩
  · exact Or.inl hall
  · right
    exact ⟨{
      tau := S.tau m
      theta := S.theta m
      stage := R.stage
      stage_pos := R.stage_pos
      stage_le := R.stage_le
      delta_le_tau := S.delta_le_tau m
      tau_le_theta := S.tau_le_theta m
      theta_le_one := S.theta_le_one m
      long := hlong
      globalValue := R.globalValue m
      adjacentValue := R.adjacentValue m
      middleValue := R.middleValue m
      global_upper := R.global_upper m
      adjacent_upper := R.adjacent_upper m
      middle_lower_with_constant := by
        intro rho hlower hupper
        exact hbarrier rho ⟨hlower, hupper⟩ }⟩

end KatzTaoConstantStoppingRun

/-! ## No-bad-scale and finite-chain adapters -/

/-- The no-further-split form matching `terminal_noConstantBad`. -/
structure KatzTaoConstantNoSplitRun
    (delta : NNReal) (depth N : Nat) (epsilon : Real)
    (eta : Nat -> Real) (K : ENNReal)
    (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  eta_stage_le_epsilon : eta stage <= epsilon
  globalValue : Fin depth -> ENNReal
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  global_upper : forall m,
    globalValue m <= (S.theta m : ENNReal) ^ (-eta (stage - 1))
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal_noConstantBad : forall m, ¬ S.IsLarge epsilon m ->
    ¬ exists rho, S.IsBuffered epsilon m rho ∧
      K * middleValue m rho <
        (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage)

namespace KatzTaoConstantNoSplitRun

variable {delta : NNReal} {depth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {K : ENNReal}
  {S : FiniteScaleSequence delta depth}

/-- Negating a constant-adjusted bad scale produces exactly the
constant-bearing terminal barrier. -/
def toStoppingRun
    (R : KatzTaoConstantNoSplitRun delta depth N epsilon eta K S) :
    KatzTaoConstantStoppingRun delta depth N epsilon eta K S where
  stage := R.stage
  stage_pos := R.stage_pos
  stage_le := R.stage_le
  eta_monotone := R.eta_monotone
  eta_stage_le_epsilon := R.eta_stage_le_epsilon
  globalValue := R.globalValue
  adjacentValue := R.adjacentValue
  middleValue := R.middleValue
  global_upper := R.global_upper
  adjacent_upper := R.adjacent_upper
  terminal := by
    intro m
    by_cases hlarge : S.IsLarge epsilon m
    · exact Or.inl hlarge
    · right
      exact lowerBound_of_no_strict_split
        (S.IsBuffered epsilon m)
        (fun rho => K * R.middleValue m rho)
        (fun rho =>
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta R.stage))
        (R.terminal_noConstantBad m hlarge)

theorem allLarge_or_witness
    (R : KatzTaoConstantNoSplitRun delta depth N epsilon eta K S) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoConstantDividingWitness delta N epsilon eta K) :=
  R.toStoppingRun.allLarge_or_witness

end KatzTaoConstantNoSplitRun

/-- The global value is backed by an actual frozen finite `Delta_max` chain;
its telescope is unchanged by the terminal constant. -/
structure KatzTaoConstantChainNoSplitRun
    (delta : NNReal) (depth chainDepth N : Nat) (epsilon : Real)
    (eta : Nat -> Real) (K : ENNReal)
    (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  eta_stage_le_epsilon : eta stage <= epsilon
  chain : Fin depth -> FiniteDeltaMaxChain chainDepth
  productBudget : forall m,
    (chain m).dimensionalLoss ^ chainDepth *
          (∏ k ∈ Finset.range chainDepth, (chain m).localDeltaMax k) <=
      (S.theta m : ENNReal) ^ (-eta (stage - 1))
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal_noConstantBad : forall m, ¬ S.IsLarge epsilon m ->
    ¬ exists rho, S.IsBuffered epsilon m rho ∧
      K * middleValue m rho <
        (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage)

namespace KatzTaoConstantChainNoSplitRun

variable {delta : NNReal} {depth chainDepth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {K : ENNReal}
  {S : FiniteScaleSequence delta depth}

/-- The existing telescope supplies the global upper bound; `K` appears
only in the terminal middle-scale lower bound. -/
def toNoSplitRun
    (R : KatzTaoConstantChainNoSplitRun
      delta depth chainDepth N epsilon eta K S) :
    KatzTaoConstantNoSplitRun delta depth N epsilon eta K S where
  stage := R.stage
  stage_pos := R.stage_pos
  stage_le := R.stage_le
  eta_monotone := R.eta_monotone
  eta_stage_le_epsilon := R.eta_stage_le_epsilon
  globalValue := fun m => (R.chain m).deltaMax 0
  adjacentValue := R.adjacentValue
  middleValue := R.middleValue
  global_upper := by
    intro m
    exact FiniteDeltaMaxChain.global_le_exponent_of_productBudget
      (R.chain m) (S.theta m) (eta (R.stage - 1)) (R.productBudget m)
  adjacent_upper := R.adjacent_upper
  terminal_noConstantBad := R.terminal_noConstantBad

theorem allLarge_or_witness
    (R : KatzTaoConstantChainNoSplitRun
      delta depth chainDepth N epsilon eta K S) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoConstantDividingWitness delta N epsilon eta K) :=
  R.toNoSplitRun.allLarge_or_witness

end KatzTaoConstantChainNoSplitRun

/-! ## Actual telescope and strict-localization endpoint -/

variable {delta : NNReal} {outerDepth chainDepth adjacentDepth N : Nat}
  {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta outerDepth}

/-- Both actual telescopes produce the unchanged global and adjacent upper
bounds; the terminal input has exactly the constant-adjusted shape produced
by actual strict localization. -/
def toActualKatzTaoConstantChainNoSplitRun_of_bufferedExponentData
    (A : ActualIntervalCovers S)
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S A adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage eta)
    (adjacentExponent :
      FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily.ExponentBudgetData
        G stage eta)
    (K : ENNReal)
    (terminal_noConstantBad : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        K * A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    KatzTaoConstantChainNoSplitRun
      delta outerDepth chainDepth N epsilon eta K S where
  stage := stage
  stage_pos := stage_pos
  stage_le := stage_le
  eta_monotone := eta_monotone
  eta_stage_le_epsilon := eta_stage_le_epsilon
  chain := B.finiteChain
  productBudget := B.productBudget_of_actual
    (fun m => (S.theta m : ENNReal) ^ (-eta (stage - 1)))
    (globalExponent.actualProductBudget B)
  adjacentValue := A.adjacentCoarseValue
  middleValue := A.coarseValueAt
  adjacent_upper := adjacentExponent.adjacent_upper G
  terminal_noConstantBad := terminal_noConstantBad

/-- Fully accounted actual global/adjacent data and a constant-bearing
terminal certificate give the finite endpoint without any loss callback. -/
theorem allLarge_or_constantWitness_of_bufferedExponentData
    (A : ActualIntervalCovers S)
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S A adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage eta)
    (adjacentExponent :
      FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily.ExponentBudgetData
        G stage eta)
    (K : ENNReal)
    (terminal_noConstantBad : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        K * A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoConstantDividingWitness delta N epsilon eta K) :=
  (toActualKatzTaoConstantChainNoSplitRun_of_bufferedExponentData
    A B G stage stage_pos stage_le eta_monotone eta_stage_le_epsilon
    globalExponent adjacentExponent K terminal_noConstantBad).allLarge_or_witness

variable {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- End-to-end callback-free Family7 endpoint.  Actual coherent geometry
produces `K = actualStrictLocalizationConstant iota`, finite node checks
produce the terminal certificate, and the two actual telescopes produce the
global and adjacent upper bounds. -/
theorem allLarge_or_constantWitness_of_actualStrictLoss
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S (C.toActualIntervalCovers S) adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage eta)
    (adjacentExponent :
      FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily.ExponentBudgetData
        G stage eta)
    (tau_pos : forall m, 0 < S.tau m)
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := eta) (stage := stage)
      (C.toActualIntervalCovers S) R)
    (hTwoEta : (2 : Real) <= eta stage) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoConstantDividingWitness delta N epsilon eta
        (actualStrictLocalizationConstant iota)) := by
  exact allLarge_or_constantWitness_of_bufferedExponentData
    (C.toActualIntervalCovers S) B G stage stage_pos stage_le eta_monotone
    eta_stage_le_epsilon globalExponent adjacentExponent
    (actualStrictLocalizationConstant iota)
    (FamilyStickyScaleChainActualStrictLossWithConstantV1.CoherentIntervalLocalizationGeometry.actual_terminal_noConstantBad
      (C := C) (R := R) tau_pos V hTwoEta eta_stage_le_epsilon)

/-! ## Exact constant-one seam -/

namespace KatzTaoConstantDividingWitness

variable {delta : NNReal} {N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {K : ENNReal}

/-- The sole extra input needed to recover the old constant-one witness is
removal of `K` from the buffered middle lower bound. -/
def toDividingWitness
    (W : KatzTaoConstantDividingWitness delta N epsilon eta K)
    (remove_constant : forall rho : NNReal,
      (W.tau : ENNReal) *
            (((W.theta / W.tau : NNReal) : ENNReal) ^ epsilon) <= rho ->
        (rho : ENNReal) <=
            (W.theta : ENNReal) *
              (((W.tau / W.theta : NNReal) : ENNReal) ^ epsilon) ->
        K * W.middleValue rho <= W.middleValue rho) :
    KatzTaoDividingWitness delta N epsilon eta where
  tau := W.tau
  theta := W.theta
  stage := W.stage
  stage_pos := W.stage_pos
  stage_le := W.stage_le
  delta_le_tau := W.delta_le_tau
  tau_le_theta := W.tau_le_theta
  theta_le_one := W.theta_le_one
  long := W.long
  globalValue := W.globalValue
  adjacentValue := W.adjacentValue
  middleValue := W.middleValue
  global_upper := W.global_upper
  adjacent_upper := W.adjacent_upper
  middle_lower := by
    intro rho hlower hupper
    exact (W.middle_lower_with_constant rho hlower hupper).trans
      (remove_constant rho hlower hupper)

/-- In particular `K <= 1` removes the constant.  For the actual geometric
constant, the available bound has the opposite orientation `1 <= K`; hence
this conversion is not automatic. -/
def toDividingWitness_of_constant_le_one
    (W : KatzTaoConstantDividingWitness delta N epsilon eta K)
    (hK : K <= 1) :
    KatzTaoDividingWitness delta N epsilon eta :=
  W.toDividingWitness fun rho _ _ => by
    simpa using (mul_le_mul' hK (le_refl (W.middleValue rho)))

end KatzTaoConstantDividingWitness

#print axioms KatzTaoConstantStoppingRun.allLarge_or_witness
#print axioms KatzTaoConstantNoSplitRun.toStoppingRun
#print axioms KatzTaoConstantNoSplitRun.allLarge_or_witness
#print axioms KatzTaoConstantChainNoSplitRun.toNoSplitRun
#print axioms KatzTaoConstantChainNoSplitRun.allLarge_or_witness
#print axioms toActualKatzTaoConstantChainNoSplitRun_of_bufferedExponentData
#print axioms allLarge_or_constantWitness_of_bufferedExponentData
#print axioms allLarge_or_constantWitness_of_actualStrictLoss
#print axioms KatzTaoConstantDividingWitness.toDividingWitness
#print axioms KatzTaoConstantDividingWitness.toDividingWitness_of_constant_le_one

end
end FamilyStickyScaleChainConstantBearingStoppingEndpointV1
