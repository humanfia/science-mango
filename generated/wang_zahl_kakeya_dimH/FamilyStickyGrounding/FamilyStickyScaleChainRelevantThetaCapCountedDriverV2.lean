import FamilyStickyGrounding.FamilyStickyScaleChainRelevantThetaCapInvariantV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainRelevantThetaCapCountedDriverV2

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainBoundedRecursiveStoppingV2
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainRelevantThetaCapInvariantV2

noncomputable section

/-!
# Cap-bearing automatic counted stopping

The original relevant counted state does not store the non-large endpoint
cap, while its successor type quantifies over every state.  Consequently an
initial cap cannot honestly manufacture that unrestricted successor.  This
module uses the correct state space: the separated-factor invariant and the
endpoint cap are carried together through every reachable step.

The resulting bounded recursion has no child-successor input.  At a bad
split it constructs the two automatic terminal bodies, their conditional
normalized bounds, the child certificate, the next factor count, and the
next endpoint-cap proof internally.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Counted relevant canonical data together with the invariant controlling
exactly its non-large upper endpoints. -/
structure RelevantThetaCappedCountedState
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (gapEpsilon : Real) (eta : Nat -> Real)
    (cap : NNReal) where
  counted : RelevantCanonicalCountedState C N gapEpsilon eta
  thetaCap : NonLargeThetaCap counted.data.scales gapEpsilon cap

namespace RelevantThetaCappedCountedState

variable (C : CoherentStickyMultiscaleCover fine) (cap : NNReal)
  (X : RelevantThetaCappedCountedState C N gapEpsilon eta cap)

def toState (delta_pos : 0 < delta) :
    RelevantEnvelopeStoppingState delta N gapEpsilon eta :=
  X.counted.toState C delta_pos

@[simp] theorem toState_stage (delta_pos : 0 < delta) :
    (X.toState C cap delta_pos).stage = X.counted.data.stage := rfl

@[simp] theorem toState_scales (delta_pos : 0 < delta) :
    (X.toState C cap delta_pos).scales = X.counted.data.scales := rfl

end RelevantThetaCappedCountedState

/-- Package any stage-one capped canonical datum as an initial state. -/
def relevantThetaCappedCountedInitialState
    (C : CoherentStickyMultiscaleCover fine)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (stage_eq : Q.stage = 1) (cap : NNReal)
    (hcap : NonLargeThetaCap Q.scales gapEpsilon cap) :
    RelevantThetaCappedCountedState C N gapEpsilon eta cap where
  counted := relevantCanonicalCountedInitialState C Q stage_eq
  thetaCap := hcap

/-- Completely automatic-body initial counted state at stage one. -/
def automaticRelevantThetaCappedCountedInitialState
    {depth : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (depth_pos : 0 < depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta) (N_pos : 1 <= N)
    (cap : NNReal)
    (hcap : NonLargeThetaCap S gapEpsilon cap)
    (eta_zero_gt_two : 2 < eta 0)
    (cap_le_threshold : cap <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota) (eta 0)) :
    RelevantThetaCappedCountedState C N gapEpsilon eta cap := by
  let Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta :=
    automaticRelevantCanonicalOneStepStoppingData_of_nonLargeThetaCap
      C S depth_pos fine_refined_nonempty delta_pos (stage := 1)
      (by omega) N_pos cap hcap (by simpa using eta_zero_gt_two)
      (by simpa using cap_le_threshold)
  refine {
    counted := relevantCanonicalCountedInitialState C Q rfl
    thetaCap := ?_ }
  change NonLargeThetaCap S gapEpsilon cap
  exact hcap

/-- At every stage below `N`, the same fixed cap is inside the explicit
automatic-body threshold and the profile exponent has room beyond two. -/
def RelevantThetaCapStageWindow
    (N : Nat) (eta : Nat -> Real) (iota : Type*) [Fintype iota]
    (cap : NNReal) : Prop :=
  forall s : Nat, 1 <= s -> s < N ->
    2 < eta s /\
      cap <= automaticOneStepSmallThetaThreshold (Fintype.card iota)
        (eta s)

/-- The child certificate generated from the current state's carried cap.
No bad-split-dependent hypothesis is accepted. -/
def RelevantThetaCappedCountedState.automaticChildCertificate
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (X : RelevantThetaCappedCountedState C N gapEpsilon eta cap)
    (stage_lt : X.counted.data.stage < N)
    (bad : RelevantSelectedActualBadSplit C (X.toState C cap delta_pos)) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos
      X.counted.data bad :=
  relevantCanonicalChildCertificate_of_nonLargeThetaCap C gap_nonneg
    delta_pos X.counted.data bad cap X.thetaCap
    (stageWindow X.counted.data.stage X.counted.data.stage_pos stage_lt).1
    (stageWindow X.counted.data.stage X.counted.data.stage_pos stage_lt).2

/-- One fully automatic cap-bearing counted step. -/
def relevantThetaCappedCountingNext
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (X : RelevantThetaCappedCountedState C N gapEpsilon eta cap) :
    Option (RelevantThetaCappedCountedState C N gapEpsilon eta cap) := by
  classical
  by_cases hbad : Nonempty
      (RelevantSelectedActualBadSplit C (X.toState C cap delta_pos))
  · have stage_lt : X.counted.data.stage < N := by
      by_contra not_lt
      have stage_eq : X.counted.data.stage = N := by
        have := X.counted.data.stage_le
        omega
      exact (no_relevant_bad_of_factorCountInvariant_at_bound
        C delta_pos delta_lt_one gap_pos exponent_budget X.counted.data
          X.counted.factorCount stage_eq) hbad
    let bad : RelevantSelectedActualBadSplit C
        (X.toState C cap delta_pos) := Classical.choice hbad
    let R := X.automaticChildCertificate C gap_pos.le delta_pos cap
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
          eta_monotone X.counted.data bad R stage_lt X.thetaCap }
  · exact none

theorem relevantThetaCappedCountingNext_eq_none_iff_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (X : RelevantThetaCappedCountedState C N gapEpsilon eta cap) :
    relevantThetaCappedCountingNext C delta_pos delta_lt_one gap_pos
        eta_monotone exponent_budget cap stageWindow X = none <->
      Not (Nonempty
        (RelevantSelectedActualBadSplit C (X.toState C cap delta_pos))) := by
  classical
  simp [relevantThetaCappedCountingNext]

theorem relevantThetaCappedCountingNext_stage
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    {X Y : RelevantThetaCappedCountedState C N gapEpsilon eta cap}
    (hnext : relevantThetaCappedCountingNext C delta_pos delta_lt_one
      gap_pos eta_monotone exponent_budget cap stageWindow X = some Y) :
    Y.counted.data.stage = X.counted.data.stage + 1 := by
  classical
  unfold relevantThetaCappedCountingNext at hnext
  split at hnext
  next hbad =>
    have state_eq := Option.some.inj hnext
    rw [<- state_eq]
    rfl
  next hbad =>
    simp at hnext

def relevantThetaCappedCountingBoundedSystem
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap) :
    BoundedSuccessorSystem
      (RelevantThetaCappedCountedState C N gapEpsilon eta cap) N where
  stage := fun X => X.counted.data.stage
  stage_le := fun X => X.counted.data.stage_le
  next := relevantThetaCappedCountingNext C delta_pos delta_lt_one gap_pos
    eta_monotone exponent_budget cap stageWindow
  stage_next := relevantThetaCappedCountingNext_stage C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget cap stageWindow

def relevantThetaCappedCountingTerminalState
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap) :
    RelevantThetaCappedCountedState C N gapEpsilon eta cap :=
  (relevantThetaCappedCountingBoundedSystem C delta_pos delta_lt_one gap_pos
    eta_monotone exponent_budget cap stageWindow).terminalState initial

theorem relevantThetaCappedCountingNext_terminalState_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap) :
    relevantThetaCappedCountingNext C delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget cap stageWindow
      (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap stageWindow initial) = none := by
  exact (relevantThetaCappedCountingBoundedSystem C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget cap stageWindow).next_terminalState_eq_none
      initial

theorem relevantThetaCappedCountingTerminalState_reachesIn
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap) :
    exists steps, steps <= N - initial.counted.data.stage /\
      (relevantThetaCappedCountingBoundedSystem C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap stageWindow).ReachesIn steps
          initial
          (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap stageWindow initial) := by
  exact (relevantThetaCappedCountingBoundedSystem C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget cap stageWindow).terminalState_reachesIn
      initial

theorem relevantThetaCappedCountingTerminalState_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap) :
    Not (Nonempty (RelevantSelectedActualBadSplit C
      ((relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap stageWindow initial).toState
          C cap delta_pos))) := by
  exact (relevantThetaCappedCountingNext_eq_none_iff_no_bad C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap stageWindow _).1
      (relevantThetaCappedCountingNext_terminalState_eq_none C delta_pos
        delta_lt_one gap_pos eta_monotone exponent_budget cap stageWindow
        initial)

/-- The automatic cap-bearing recursion terminates with the literal no-split
statement consumed by the recovered endpoint. -/
theorem relevantThetaCappedCountingTerminalState_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap) :
    forall not_all_large : Not
        ((relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales.AllStepsLarge
            gapEpsilon),
      SelectedActualTerminalNoSplit
        (C.toActualIntervalCovers
          (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales)
        gapEpsilon eta
        (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.stage
        (firstNonLargeStep
          (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales
          gapEpsilon not_all_large) := by
  exact (relevant_no_bad_iff_terminalNoSplit C _).1
    (relevantThetaCappedCountingTerminalState_no_bad C delta_pos delta_lt_one
      gap_pos eta_monotone exponent_budget cap stageWindow initial)

/-- The terminal cap-bearing state retains the relevant global-product
bound at the exact first non-large interval. -/
theorem relevantThetaCappedCountingTerminalState_actualGlobalProductAt_firstNonLarge_le
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap)
    (not_all_large : Not
      ((relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales.AllStepsLarge
          gapEpsilon)) :
    actualGlobalProductAt
        ((relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.buffered
            C delta_pos)
        (firstNonLargeStep
          (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales
          gapEpsilon not_all_large) <=
      requiredGlobalPowerAt
        (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales
        eta
        (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.stage
        (firstNonLargeStep
          (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales
          gapEpsilon not_all_large) := by
  let terminal := relevantThetaCappedCountingTerminalState C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap stageWindow initial
  exact (terminal.toState C cap delta_pos).actualGlobalProductAt_firstNonLarge_le
    not_all_large

#print axioms automaticRelevantThetaCappedCountedInitialState
#print axioms RelevantThetaCappedCountedState.automaticChildCertificate
#print axioms relevantThetaCappedCountingNext_eq_none_iff_no_bad
#print axioms relevantThetaCappedCountingNext_stage
#print axioms relevantThetaCappedCountingNext_terminalState_eq_none
#print axioms relevantThetaCappedCountingTerminalState_reachesIn
#print axioms relevantThetaCappedCountingTerminalState_no_bad
#print axioms relevantThetaCappedCountingTerminalState_terminalNoSplit
#print axioms relevantThetaCappedCountingTerminalState_actualGlobalProductAt_firstNonLarge_le

end
end FamilyStickyScaleChainRelevantThetaCapCountedDriverV2
