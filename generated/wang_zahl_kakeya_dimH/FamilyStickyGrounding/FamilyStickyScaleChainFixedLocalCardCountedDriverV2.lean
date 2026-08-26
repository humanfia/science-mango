import FamilyStickyGrounding.FamilyStickyScaleChainFixedLocalCardAutomaticSuccessorV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFixedLocalCardCountedDriverV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainBoundedRecursiveStoppingV2
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2
open FamilyStickyScaleChainRelevantThetaCapInvariantV2
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainLocalCardBudgetInvariantV2
open FamilyStickyScaleChainFixedLocalCardAutomaticSuccessorV2
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# Fixed-local-card automatic counted stopping

The state space carries both invariants queried by the automatic child
producer: a cap on every non-large upper endpoint and a fixed natural upper
bound `n` on every non-large local active-card count.  Both invariants are
preserved by the literal buffered insertion, so the recursion requires no
statewise callback and no per-split child certificate.

The initial canonical envelope below calls the fixed-`n` analytic atom
directly.  Thus the automatic threshold in this module contains `n`, never
the ambient finite-type cardinality.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Fixed-local-card state and automatic initial data -/

/-- Counted canonical data carrying both the non-large endpoint cap and the
fixed local-card budget used by the analytic producer. -/
structure RelevantFixedLocalCardCountedState
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (gapEpsilon : Real) (eta : Nat -> Real)
    (cap : NNReal) (n : Nat) where
  counted : RelevantCanonicalCountedState C N gapEpsilon eta
  thetaCap : NonLargeThetaCap counted.data.scales gapEpsilon cap
  localCardBudget :
    NonLargeLocalCardBudget C counted.data.scales gapEpsilon n

namespace RelevantFixedLocalCardCountedState

variable (C : CoherentStickyMultiscaleCover fine) (cap : NNReal) (n : Nat)
  (X : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n)

def toState (delta_pos : 0 < delta) :
    RelevantEnvelopeStoppingState delta N gapEpsilon eta :=
  X.counted.toState C delta_pos

@[simp] theorem toState_stage (delta_pos : 0 < delta) :
    (X.toState C cap n delta_pos).stage = X.counted.data.stage := rfl

@[simp] theorem toState_scales (delta_pos : 0 < delta) :
    (X.toState C cap n delta_pos).scales = X.counted.data.scales := rfl

end RelevantFixedLocalCardCountedState

/-- Package any stage-one canonical datum with the two carried invariants. -/
def relevantFixedLocalCardCountedInitialState
    (C : CoherentStickyMultiscaleCover fine)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (stage_eq : Q.stage = 1) (cap : NNReal) (n : Nat)
    (hcap : NonLargeThetaCap Q.scales gapEpsilon cap)
    (hlocal : NonLargeLocalCardBudget C Q.scales gapEpsilon n) :
    RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n where
  counted := relevantCanonicalCountedInitialState C Q stage_eq
  thetaCap := hcap
  localCardBudget := hlocal

/-- Fixed-`n` automatic terminal-unit bodies satisfy the relevant envelope
on an initially capped, locally card-bounded scale sequence. -/
theorem automaticCanonicalRelevantEnvelope_upper_of_fixedLocalCardBudget
    {depth stage : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (cap : NNReal) (n : Nat)
    (hcap : NonLargeThetaCap S gapEpsilon cap)
    (hlocal : NonLargeLocalCardBudget C S gapEpsilon n)
    (profile_gt_two : 2 < eta (stage - 1))
    (cap_le_threshold : cap <=
      automaticOneStepSmallThetaThreshold n (eta (stage - 1))) :
    forall m : Fin depth, Not (S.IsLarge gapEpsilon m) ->
      canonicalHierarchyEnvelopeAt
          (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S
            fine_refined_nonempty)
          (by omega)
          (fun k => canonicalTerminalUnitBody
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S
              fine_refined_nonempty).hierarchy k)) m <=
        requiredGlobalPowerAt S eta stage m := by
  intro m not_large
  let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S
    fine_refined_nonempty
  let body : Fin depth -> ConvexBody Space :=
    fun k => canonicalTerminalUnitBody (F.hierarchy k)
  let bound :=
    ofFiniteScaleSequence_automatic_oneStepExponentBound_of_fixedCardSmallTheta
      C S fine_refined_nonempty delta_pos eta stage m n
      (NonLargeLocalCardBudget.canonicalLocalCard_le C
        fine_refined_nonempty hlocal m not_large)
      profile_gt_two ((hcap m not_large).trans cap_le_threshold)
  have body_volume_pos : forall k,
      0 < volume (body k : Set Space) := by
    intro k
    exact canonicalTerminalUnitBody_volume_pos _
  have theta_le_one : (S.theta m : ENNReal) <= 1 := by
    exact_mod_cast S.theta_le_one m
  change canonicalHierarchyEnvelopeAt F (by omega) body m <=
    requiredGlobalPowerAt S eta stage m
  calc
    canonicalHierarchyEnvelopeAt F (by omega) body m =
        canonicalOneStepNormalizedTerminalAt C F body m :=
      canonicalHierarchyEnvelopeAt_one_eq_normalizedTerminal C F delta_pos
        body body_volume_pos m
    _ <= (S.theta m : ENNReal) ^ bound.exponent :=
      bound.normalizedTerminal_upper
    _ <= (S.theta m : ENNReal) ^ (-eta (stage - 1)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge theta_le_one
        bound.exponent_balance
    _ = requiredGlobalPowerAt S eta stage m := rfl

/-- Initial relevant canonical stopping data whose analytic proof uses the
fixed local-card budget rather than the ambient finite type cardinality. -/
def automaticRelevantCanonicalOneStepStoppingData_of_fixedLocalCardBudget
    {depth stage : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (depth_pos : 0 < depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (cap : NNReal) (n : Nat)
    (hcap : NonLargeThetaCap S gapEpsilon cap)
    (hlocal : NonLargeLocalCardBudget C S gapEpsilon n)
    (profile_gt_two : 2 < eta (stage - 1))
    (cap_le_threshold : cap <=
      automaticOneStepSmallThetaThreshold n (eta (stage - 1))) :
    RelevantCanonicalOneStepStoppingData C N gapEpsilon eta where
  depth := depth
  depth_pos := depth_pos
  fine_refined_nonempty := fine_refined_nonempty
  scales := S
  stage := stage
  stage_pos := stage_pos
  stage_le := stage_le
  initialBody := fun m => canonicalTerminalUnitBody
    ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S
      fine_refined_nonempty).hierarchy m)
  initialVolume_pos := fun _m => canonicalTerminalUnitBody_volume_pos _
  terminal_top_le_one := fun _m => canonicalTerminalUnitBody_top_le_one _
  canonicalRelevantEnvelope_upper :=
    automaticCanonicalRelevantEnvelope_upper_of_fixedLocalCardBudget C S
      fine_refined_nonempty delta_pos cap n hcap hlocal profile_gt_two
      cap_le_threshold

/-- Completely automatic-body initial counted state at stage one, retaining
both input invariants. -/
def automaticRelevantFixedLocalCardCountedInitialState
    {depth : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (depth_pos : 0 < depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta) (N_pos : 1 <= N)
    (cap : NNReal) (n : Nat)
    (hcap : NonLargeThetaCap S gapEpsilon cap)
    (hlocal : NonLargeLocalCardBudget C S gapEpsilon n)
    (eta_zero_gt_two : 2 < eta 0)
    (cap_le_threshold : cap <=
      automaticOneStepSmallThetaThreshold n (eta 0)) :
    RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n := by
  let Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta :=
    automaticRelevantCanonicalOneStepStoppingData_of_fixedLocalCardBudget
      C S depth_pos fine_refined_nonempty delta_pos (stage := 1)
      (by omega) N_pos cap n hcap hlocal
      (by simpa using eta_zero_gt_two)
      (by simpa using cap_le_threshold)
  refine {
    counted := relevantCanonicalCountedInitialState C Q rfl
    thetaCap := ?_
    localCardBudget := ?_ }
  · change NonLargeThetaCap S gapEpsilon cap
    exact hcap
  · change NonLargeLocalCardBudget C S gapEpsilon n
    exact hlocal

/-! ## Fixed-local-card transition -/

/-- At each stage below `N`, the carried cap lies inside the fixed-`n`
automatic threshold and the profile exponent has room beyond two. -/
def RelevantFixedLocalCardStageWindow
    (N : Nat) (eta : Nat -> Real) (cap : NNReal) (n : Nat) : Prop :=
  forall s : Nat, 1 <= s -> s < N ->
    2 < eta s /\
      cap <= automaticOneStepSmallThetaThreshold n (eta s)

/-- The fixed-local-card child conditions generated internally from the two
carried invariants. -/
theorem RelevantFixedLocalCardCountedState.automaticChildConditions
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (X : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n)
    (stage_lt : X.counted.data.stage < N)
    (bad : RelevantSelectedActualBadSplit C
      (X.toState C cap n delta_pos)) :
    RelevantFixedLocalCardAutomaticChildConditions C gap_nonneg delta_pos
      X.counted.data bad n := by
  let refinedCap : NonLargeThetaCap
      (relevantInsertedScales C gap_nonneg delta_pos X.counted.data bad)
      gapEpsilon cap := by
    exact NonLargeThetaCap.refinedScales C gap_nonneg delta_pos
      (X.counted.data.toState C delta_pos) bad X.thetaCap
  let refinedBudget : NonLargeLocalCardBudget C
      (relevantInsertedScales C gap_nonneg delta_pos X.counted.data bad)
      gapEpsilon n := by
    exact NonLargeLocalCardBudget.refinedScales C gap_nonneg delta_pos
      (X.counted.data.toState C delta_pos) bad X.localCardBudget
  have window := stageWindow X.counted.data.stage
    X.counted.data.stage_pos stage_lt
  refine {
    upper := fun child_not_large =>
      ⟨window.1, ?_, ?_⟩
    lower := fun child_not_large =>
      ⟨window.1, ?_, ?_⟩ }
  · exact
      NonLargeLocalCardBudget.canonicalLocalCard_le C
        X.counted.data.fine_refined_nonempty refinedBudget
        (upperChildIndex (relevantSelectedStep C delta_pos X.counted.data bad))
        child_not_large
  · exact (refinedCap
      (upperChildIndex (relevantSelectedStep C delta_pos X.counted.data bad))
      child_not_large).trans window.2
  · exact
      NonLargeLocalCardBudget.canonicalLocalCard_le C
        X.counted.data.fine_refined_nonempty refinedBudget
        (lowerChildIndex (relevantSelectedStep C delta_pos X.counted.data bad))
        child_not_large
  · exact (refinedCap
      (lowerChildIndex (relevantSelectedStep C delta_pos X.counted.data bad))
      child_not_large).trans window.2

/-- The canonical child certificate generated from the current state's two
invariants and the fixed-`n` stage window. -/
def RelevantFixedLocalCardCountedState.automaticChildCertificate
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (X : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n)
    (stage_lt : X.counted.data.stage < N)
    (bad : RelevantSelectedActualBadSplit C
      (X.toState C cap n delta_pos)) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos
      X.counted.data bad :=
  relevantCanonicalChildCertificate_of_fixedLocalCardSmallTheta C
    gap_nonneg delta_pos X.counted.data bad n
    (X.automaticChildConditions C gap_nonneg delta_pos cap n stageWindow
      stage_lt bad)

/-- One fully automatic counted step with a fixed local-card budget. -/
def relevantFixedLocalCardCountingNext
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (X : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) :
    Option (RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) := by
  classical
  by_cases hbad : Nonempty
      (RelevantSelectedActualBadSplit C
        (X.toState C cap n delta_pos))
  · have stage_lt : X.counted.data.stage < N := by
      by_contra not_lt
      have stage_eq : X.counted.data.stage = N := by
        have := X.counted.data.stage_le
        omega
      exact (no_relevant_bad_of_factorCountInvariant_at_bound
        C delta_pos delta_lt_one gap_pos exponent_budget X.counted.data
          X.counted.factorCount stage_eq) hbad
    let bad : RelevantSelectedActualBadSplit C
        (X.toState C cap n delta_pos) := Classical.choice hbad
    let R := X.automaticChildCertificate C gap_pos.le delta_pos cap n
      stageWindow stage_lt bad
    exact some
      { counted :=
          { data := R.toCanonical C gap_pos.le delta_pos X.counted.data bad
              eta_monotone stage_lt
            factorCount :=
              relevantCanonicalFactorCountInvariant_toCanonical C gap_pos.le
                delta_pos gap_pos eta_monotone X.counted.data bad R stage_lt
                X.counted.factorCount }
        thetaCap := nonLargeThetaCap_toCanonical C gap_pos.le delta_pos
          eta_monotone X.counted.data bad R stage_lt X.thetaCap
        localCardBudget := by
          change NonLargeLocalCardBudget C
            (bad.refinedScales C (X.toState C cap n delta_pos)
              gap_pos.le delta_pos) gapEpsilon n
          exact NonLargeLocalCardBudget.refinedScales C gap_pos.le delta_pos
            (X.toState C cap n delta_pos) bad X.localCardBudget }
  · exact none

theorem relevantFixedLocalCardCountingNext_eq_none_iff_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (X : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) :
    relevantFixedLocalCardCountingNext C delta_pos delta_lt_one gap_pos
        eta_monotone exponent_budget cap n stageWindow X = none <->
      Not (Nonempty
        (RelevantSelectedActualBadSplit C
          (X.toState C cap n delta_pos))) := by
  classical
  simp [relevantFixedLocalCardCountingNext]

theorem relevantFixedLocalCardCountingNext_stage
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    {X Y : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n}
    (hnext : relevantFixedLocalCardCountingNext C delta_pos delta_lt_one
      gap_pos eta_monotone exponent_budget cap n stageWindow X = some Y) :
    Y.counted.data.stage = X.counted.data.stage + 1 := by
  classical
  unfold relevantFixedLocalCardCountingNext at hnext
  split at hnext
  next hbad =>
    have state_eq := Option.some.inj hnext
    rw [<- state_eq]
    rfl
  next hbad =>
    simp at hnext

/-! ## Bounded recursion and terminal APIs -/

def relevantFixedLocalCardCountingBoundedSystem
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n) :
    BoundedSuccessorSystem
      (RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) N where
  stage := fun X => X.counted.data.stage
  stage_le := fun X => X.counted.data.stage_le
  next := relevantFixedLocalCardCountingNext C delta_pos delta_lt_one gap_pos
    eta_monotone exponent_budget cap n stageWindow
  stage_next := relevantFixedLocalCardCountingNext_stage C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap n stageWindow

def relevantFixedLocalCardCountingTerminalState
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) :
    RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n :=
  (relevantFixedLocalCardCountingBoundedSystem C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget cap n stageWindow).terminalState initial

theorem relevantFixedLocalCardCountingNext_terminalState_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) :
    relevantFixedLocalCardCountingNext C delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget cap n stageWindow
      (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap n stageWindow initial) = none := by
  exact (relevantFixedLocalCardCountingBoundedSystem C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget cap n stageWindow).next_terminalState_eq_none
      initial

theorem relevantFixedLocalCardCountingTerminalState_reachesIn
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) :
    exists steps, steps <= N - initial.counted.data.stage /\
      (relevantFixedLocalCardCountingBoundedSystem C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap n stageWindow).ReachesIn steps
          initial
          (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap n stageWindow initial) := by
  exact (relevantFixedLocalCardCountingBoundedSystem C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget cap n stageWindow).terminalState_reachesIn
      initial

theorem relevantFixedLocalCardCountingTerminalState_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) :
    Not (Nonempty (RelevantSelectedActualBadSplit C
      ((relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap n stageWindow initial).toState
          C cap n delta_pos))) := by
  exact (relevantFixedLocalCardCountingNext_eq_none_iff_no_bad C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap n stageWindow _).1
      (relevantFixedLocalCardCountingNext_terminalState_eq_none C delta_pos
        delta_lt_one gap_pos eta_monotone exponent_budget cap n stageWindow
        initial)

/-- The fixed-local-card recursion terminates with the literal no-split
statement consumed by the recovered endpoint. -/
theorem relevantFixedLocalCardCountingTerminalState_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n) :
    forall not_all_large : Not
        ((relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.scales.AllStepsLarge
            gapEpsilon),
      SelectedActualTerminalNoSplit
        (C.toActualIntervalCovers
          (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.scales)
        gapEpsilon eta
        (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.stage
        (firstNonLargeStep
          (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.scales
          gapEpsilon not_all_large) := by
  exact (relevant_no_bad_iff_terminalNoSplit C _).1
    (relevantFixedLocalCardCountingTerminalState_no_bad C delta_pos
      delta_lt_one gap_pos eta_monotone exponent_budget cap n stageWindow
      initial)

/-- The terminal state retains the relevant global-product bound at the
exact first non-large interval. -/
theorem relevantFixedLocalCardCountingTerminalState_actualGlobalProductAt_firstNonLarge_le
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState C N gapEpsilon eta cap n)
    (not_all_large : Not
      ((relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.scales.AllStepsLarge
          gapEpsilon)) :
    actualGlobalProductAt
        ((relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.buffered
            C delta_pos)
        (firstNonLargeStep
          (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.scales
          gapEpsilon not_all_large) <=
      requiredGlobalPowerAt
        (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.scales
        eta
        (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.stage
        (firstNonLargeStep
          (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap n stageWindow initial).counted.data.scales
          gapEpsilon not_all_large) := by
  let terminal := relevantFixedLocalCardCountingTerminalState C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap n stageWindow initial
  exact (terminal.toState C cap n delta_pos).actualGlobalProductAt_firstNonLarge_le
    not_all_large

#print axioms automaticCanonicalRelevantEnvelope_upper_of_fixedLocalCardBudget
#print axioms automaticRelevantCanonicalOneStepStoppingData_of_fixedLocalCardBudget
#print axioms automaticRelevantFixedLocalCardCountedInitialState
#print axioms RelevantFixedLocalCardCountedState.automaticChildConditions
#print axioms RelevantFixedLocalCardCountedState.automaticChildCertificate
#print axioms relevantFixedLocalCardCountingNext_eq_none_iff_no_bad
#print axioms relevantFixedLocalCardCountingNext_stage
#print axioms relevantFixedLocalCardCountingNext_terminalState_eq_none
#print axioms relevantFixedLocalCardCountingTerminalState_reachesIn
#print axioms relevantFixedLocalCardCountingTerminalState_no_bad
#print axioms relevantFixedLocalCardCountingTerminalState_terminalNoSplit
#print axioms relevantFixedLocalCardCountingTerminalState_actualGlobalProductAt_firstNonLarge_le

end
end FamilyStickyScaleChainFixedLocalCardCountedDriverV2
