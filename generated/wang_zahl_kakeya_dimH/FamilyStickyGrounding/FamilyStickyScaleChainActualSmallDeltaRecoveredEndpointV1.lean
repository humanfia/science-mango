import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1

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
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Actual stopping output with automatic small-delta recovery

The actual constant-bearing stopping pipeline already constructs a dividing
witness, but its public endpoint returns only `Nonempty W`.  That proposition
forgets the definitional fact that the constructed witness has the stopping
run's selected stage.  The first result below faithfully repeats only the
finite selection step and retains this equality in the output.

The actual strict-localization constant is then proved finite from its
definition.  Running the real global, adjacent, and finite-node producers with
the half-room reserved profile gives the source dichotomy

`all steps large` or `recovered literal witness`.

No witness, stage equality, terminal callback, scale positivity certificate,
or constant finiteness proof is supplied by the caller.  The unavoidable
remaining branch is the original stopping dichotomy: a literal dividing
witness follows directly once `AllStepsLarge` is ruled out.
-/

/-! ## Stage-preserving finite stopping -/

namespace StoppingRun

variable {delta : NNReal} {depth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {K : ENNReal}
  {S : FiniteScaleSequence delta depth}

/-- The same finite selection used by the existing stopping endpoint, with
the construction's stage equality retained rather than erased by
`Nonempty`. -/
theorem allLarge_or_exists_witness_with_stage
    (R : KatzTaoConstantStoppingRun delta depth N epsilon eta K S) :
    S.AllStepsLarge epsilon ∨
      ∃ W : KatzTaoConstantDividingWitness delta N epsilon eta K,
        W.stage = R.stage := by
  let barrier : Fin depth -> Prop := fun m =>
    forall rho, S.IsBuffered epsilon m rho ->
      (((S.theta m / rho : NNReal) : ENNReal) ^ eta R.stage) <=
        K * R.middleValue m rho
  rcases S.allStepsLarge_or_exists_long epsilon barrier R.terminal with
    hall | ⟨m, hlong, hbarrier⟩
  · exact Or.inl hall
  · right
    refine ⟨{
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
      middle_lower_with_constant := ?_ }, rfl⟩
    intro rho lower upper
    exact hbarrier rho ⟨lower, upper⟩

end StoppingRun

namespace ChainNoSplitRun

variable {delta : NNReal} {depth chainDepth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {K : ENNReal}
  {S : FiniteScaleSequence delta depth}

/-- The actual chain/no-split run retains its selected stage through the two
existing structural adapters and the strengthened finite selection. -/
theorem allLarge_or_exists_witness_with_stage
    (R : KatzTaoConstantChainNoSplitRun
      delta depth chainDepth N epsilon eta K S) :
    S.AllStepsLarge epsilon ∨
      ∃ W : KatzTaoConstantDividingWitness delta N epsilon eta K,
        W.stage = R.stage := by
  rcases StoppingRun.allLarge_or_exists_witness_with_stage
      R.toNoSplitRun.toStoppingRun with hall | ⟨W, W_stage⟩
  · exact Or.inl hall
  · exact Or.inr ⟨W, W_stage⟩

end ChainNoSplitRun

/-! ## Finiteness and the explicit actual threshold -/

/-- The geometric strict-localization constant is finite because it is a
maximum of one and a product of a finite cardinality with fixed numerals. -/
theorem actualStrictLocalizationConstant_ne_top
    (iota : Type*) [Fintype iota] :
    actualStrictLocalizationConstant iota ≠ ∞ := by
  simp [actualStrictLocalizationConstant, actualLocalLossConstant,
    capturedTubeBoxDimensionalConstant]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by norm_num)

/-- The half-room threshold with the actual finite-family/dimensional
constant substituted for `K`. -/
def actualStrictLossRecoveredSmallDeltaThreshold
    (eta : Nat -> Real) (stage : Nat) (epsilon : Real)
    (iota : Type*) [Fintype iota] : NNReal :=
  recoveredReservedProfileSmallDeltaThreshold eta stage epsilon
    (actualStrictLocalizationConstant iota)

theorem actualStrictLossRecoveredSmallDeltaThreshold_pos
    (eta : Nat -> Real) (stage : Nat) (epsilon : Real)
    (iota : Type*) [Fintype iota] :
    0 < actualStrictLossRecoveredSmallDeltaThreshold
      eta stage epsilon iota :=
  recoveredReservedProfileSmallDeltaThreshold_pos eta stage epsilon
    (actualStrictLocalizationConstant iota)

theorem actualStrictLossRecoveredSmallDeltaThreshold_le_one
    {eta : Nat -> Real} {stage : Nat} {epsilon : Real}
    (iota : Type*) [Fintype iota]
    (epsilon_pos : 0 < epsilon) (strict_room : eta stage < epsilon) :
    actualStrictLossRecoveredSmallDeltaThreshold eta stage epsilon iota <= 1 :=
  recoveredReservedProfileSmallDeltaThreshold_le_one
    (actualStrictLocalizationConstant iota) epsilon_pos strict_room

/-! ## Actual pipeline composition -/

variable {delta : NNReal} {outerDepth chainDepth adjacentDepth N : Nat}
  {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta outerDepth}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Full actual Family7 composition.  The target profile is raised by the
canonical half-room loss before the actual stopping run.  Finite stopping
then either certifies that every adjacent interval is large or supplies a
constant-bearing witness at the declared stage; the explicit small-delta
threshold converts the latter to the recovered literal profile.

The lower bound on the reserved stage exponent is the primitive input
required by the current quadratic strict-localization producer.  Together
with the automatically proved room inequality it also gives
`0 < epsilon`. -/
theorem room_and_allLarge_or_recoveredLiteralWitness_of_actualStrictLoss
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S (C.toActualIntervalCovers S) adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (strict_room : eta stage < epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage
          (reserveTailLoss eta stage
            (halfReservedExponentRoom eta stage epsilon)))
    (adjacentExponent :
      FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily.ExponentBudgetData
        G stage
          (reserveTailLoss eta stage
            (halfReservedExponentRoom eta stage epsilon)))
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon)
      (eta := reserveTailLoss eta stage
        (halfReservedExponentRoom eta stage epsilon))
      (stage := stage) (C.toActualIntervalCovers S) R)
    (two_le_reservedExponent : (2 : Real) <=
      eta stage + halfReservedExponentRoom eta stage epsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta stage epsilon iota) :
    eta stage + halfReservedExponentRoom eta stage epsilon <= epsilon ∧
      (S.AllStepsLarge epsilon ∨
        Nonempty (KatzTaoDividingWitness delta N epsilon
          (recoveredReservedProfile eta stage
            (halfReservedExponentRoom eta stage epsilon)))) := by
  let loss : Real := halfReservedExponentRoom eta stage epsilon
  let reservedEta : Nat -> Real := reserveTailLoss eta stage loss
  have loss_pos : 0 < loss := by
    exact halfReservedExponentRoom_pos strict_room
  have room : eta stage + loss <= epsilon := by
    exact eta_add_halfReservedExponentRoom_le strict_room
  have epsilon_pos : 0 < epsilon := by
    linarith
  have reserved_monotone : Monotone reservedEta := by
    exact reserveTailLoss_monotone eta_monotone loss_pos.le
  have reserved_stage_le : reservedEta stage <= epsilon := by
    exact reserveTailLoss_stage_le room
  have two_le_reserved : (2 : Real) <= reservedEta stage := by
    change (2 : Real) <= reserveTailLoss eta stage loss stage
    rw [reserveTailLoss_at]
    exact two_le_reservedExponent
  have sequence_tau_pos : forall m, 0 < S.tau m := by
    intro m
    exact delta_pos.trans_le (S.delta_le_tau m)
  have terminal_noConstantBad : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        actualStrictLocalizationConstant iota *
            (C.toActualIntervalCovers S).coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ reservedEta stage)) := by
    exact
      FamilyStickyScaleChainActualStrictLossWithConstantV1.CoherentIntervalLocalizationGeometry.actual_terminal_noConstantBad
        (C := C) (R := R) sequence_tau_pos V two_le_reserved
          reserved_stage_le
  let actualRun : KatzTaoConstantChainNoSplitRun
      delta outerDepth chainDepth N epsilon reservedEta
        (actualStrictLocalizationConstant iota) S :=
    toActualKatzTaoConstantChainNoSplitRun_of_bufferedExponentData
      (C.toActualIntervalCovers S) B G stage stage_pos stage_le
        reserved_monotone reserved_stage_le globalExponent adjacentExponent
        (actualStrictLocalizationConstant iota) terminal_noConstantBad
  refine ⟨room, ?_⟩
  rcases ChainNoSplitRun.allLarge_or_exists_witness_with_stage actualRun with
    hall | ⟨W, W_stage⟩
  · exact Or.inl hall
  · right
    change W.stage = stage at W_stage
    have W_tau_pos : 0 < W.tau :=
      delta_pos.trans_le W.delta_le_tau
    have threshold : delta <=
        recoveredReservedProfileSmallDeltaThreshold eta stage epsilon
          (actualStrictLocalizationConstant iota) := by
      exact delta_le
    exact exists_literalWitness_for_halfRoomRecoveredProfile W W_stage
      (actualStrictLocalizationConstant_ne_top iota) epsilon_pos strict_room
      delta_pos W_tau_pos threshold

/-- Direct recovered-witness endpoint for the dividing branch.  The only
extra proposition rules out the other, genuinely present branch of the
finite stopping dichotomy; no constant-bearing witness or any of its fields
is supplied. -/
theorem exists_recoveredLiteralWitness_of_actualStrictLoss
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S (C.toActualIntervalCovers S) adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (strict_room : eta stage < epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage
          (reserveTailLoss eta stage
            (halfReservedExponentRoom eta stage epsilon)))
    (adjacentExponent :
      FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily.ExponentBudgetData
        G stage
          (reserveTailLoss eta stage
            (halfReservedExponentRoom eta stage epsilon)))
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon)
      (eta := reserveTailLoss eta stage
        (halfReservedExponentRoom eta stage epsilon))
      (stage := stage) (C.toActualIntervalCovers S) R)
    (two_le_reservedExponent : (2 : Real) <=
      eta stage + halfReservedExponentRoom eta stage epsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta stage epsilon iota)
    (not_all_large : ¬ S.AllStepsLarge epsilon) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta stage
        (halfReservedExponentRoom eta stage epsilon))) := by
  have result :=
    room_and_allLarge_or_recoveredLiteralWitness_of_actualStrictLoss
      C R B G stage stage_pos stage_le eta_monotone strict_room
        globalExponent adjacentExponent V two_le_reservedExponent delta_pos delta_le
  exact result.2.resolve_left not_all_large

#print axioms StoppingRun.allLarge_or_exists_witness_with_stage
#print axioms ChainNoSplitRun.allLarge_or_exists_witness_with_stage
#print axioms actualStrictLocalizationConstant_ne_top
#print axioms actualStrictLossRecoveredSmallDeltaThreshold_pos
#print axioms actualStrictLossRecoveredSmallDeltaThreshold_le_one
#print axioms room_and_allLarge_or_recoveredLiteralWitness_of_actualStrictLoss
#print axioms exists_recoveredLiteralWitness_of_actualStrictLoss

end
end FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
