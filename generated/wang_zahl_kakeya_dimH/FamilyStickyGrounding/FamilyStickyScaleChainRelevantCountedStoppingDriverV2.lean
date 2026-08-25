import FamilyStickyGrounding.FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
import FamilyStickyGrounding.FamilyStickyScaleChainLastStageCountingBoundV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainRelevantCountedStoppingDriverV2

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainBoundedRecursiveStoppingV2
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open FamilyStickyScaleChainLastStageCountingBoundV2
open FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2

noncomputable section

/-!
# Relevant canonical counted stopping driver

The canonical relevant-envelope state asks for an envelope estimate only on
intervals which can be selected by the stopping argument.  This file equips
that state with the separated-factor history invariant and runs the bounded
literal-insertion recursion.

No `NoBadAtStageBound` hypothesis occurs.  At stage `N`, a further buffered
non-large insertion would create at least `N` uniformly separated adjacent
factors, contradicting the exact endpoint telescope.  The analytic successor
is queried only for a `RelevantCanonicalChildCertificate`; in particular its
two child envelope estimates are conditional on the corresponding child
being non-large.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Relevant literal insertions and the counting potential -/

/-- A literal bad split of a relevant-envelope state raises the separated
factor count by at least one.  This uses only the selected interval's
non-largeness and buffered-radius data; its strict analytic deficit is not
needed by the scale calculation. -/
theorem relevantBadSplit_separatedFactorCount_succ_le
    (C : CoherentStickyMultiscaleCover fine)
    (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C X)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (gap_pos : 0 < gapEpsilon) :
    separatedFactorCount (lastStageRatioFloor delta gapEpsilon) X.scales + 1 <=
      separatedFactorCount (lastStageRatioFloor delta gapEpsilon)
        (bad.refinedScales C X gap_nonneg delta_pos) := by
  have href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  have children := lastStageRatioFloor_le_childRatios
    X.scales bad.selectedStep bad.rho
      (bad.refinedScales C X gap_nonneg delta_pos)
      delta_pos gap_pos bad.selectedStep_not_large bad.rho_buffered href
  exact separatedFactorCount_succ_le_of_refinesAt
    (lastStageRatioFloor delta gapEpsilon) X.scales bad.selectedStep bad.rho
      (bad.refinedScales C X gap_nonneg delta_pos) href children.1 children.2

/-- The history invariant recorded directly on relevant canonical data. -/
def RelevantCanonicalFactorCountInvariant
    {C : CoherentStickyMultiscaleCover fine}
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta) : Prop :=
  Q.stage - 1 <=
    separatedFactorCount (lastStageRatioFloor delta gapEpsilon) Q.scales

/-- Every stage-one relevant canonical datum has the initial history
invariant. -/
theorem relevantCanonicalFactorCountInvariant_of_stage_eq_one
    (C : CoherentStickyMultiscaleCover fine)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (stage_eq : Q.stage = 1) :
    RelevantCanonicalFactorCountInvariant Q := by
  unfold RelevantCanonicalFactorCountInvariant
  omega

/-- Canonical insertion preserves the counting invariant.  The child
certificate supplies geometry, while literal scale insertion supplies the
one-unit growth of the integer potential. -/
theorem relevantCanonicalFactorCountInvariant_toCanonical
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C (Q.toState C delta_pos))
    (R : RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad)
    (stage_lt : Q.stage < N)
    (hQ : RelevantCanonicalFactorCountInvariant Q) :
    RelevantCanonicalFactorCountInvariant
      (R.toCanonical C gap_nonneg delta_pos Q bad eta_monotone stage_lt) := by
  have growth := relevantBadSplit_separatedFactorCount_succ_le
    C (Q.toState C delta_pos) bad gap_nonneg delta_pos gap_pos
  unfold RelevantCanonicalFactorCountInvariant at hQ ⊢
  change Q.stage - 1 <=
      separatedFactorCount (lastStageRatioFloor delta gapEpsilon) Q.scales at hQ
  change Q.stage + 1 - 1 <=
    separatedFactorCount (lastStageRatioFloor delta gapEpsilon)
      (bad.refinedScales C (Q.toState C delta_pos)
        gap_nonneg delta_pos)
  calc
    Q.stage + 1 - 1 = Q.stage := by omega
    _ = Q.stage - 1 + 1 := (Nat.sub_add_cancel Q.stage_pos).symm
    _ <= separatedFactorCount
        (lastStageRatioFloor delta gapEpsilon) Q.scales + 1 :=
      Nat.add_le_add_right hQ 1
    _ <= separatedFactorCount (lastStageRatioFloor delta gapEpsilon)
        (bad.refinedScales C (Q.toState C delta_pos)
          gap_nonneg delta_pos) := growth

/-- At stage `N`, the exact ratio telescope rules out any relevant literal
bad split.  This is the last-stage contradiction used by the recursion, not
an assumed `NoBadAtStageBound`. -/
theorem no_relevant_bad_of_factorCountInvariant_at_bound
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (hQ : RelevantCanonicalFactorCountInvariant Q)
    (stage_eq : Q.stage = N) :
    Not (Nonempty
      (RelevantSelectedActualBadSplit C (Q.toState C delta_pos))) := by
  rintro ⟨bad⟩
  have growth := relevantBadSplit_separatedFactorCount_succ_le
    C (Q.toState C delta_pos) bad gap_pos.le delta_pos gap_pos
  change separatedFactorCount
      (lastStageRatioFloor delta gapEpsilon) Q.scales + 1 <=
    separatedFactorCount (lastStageRatioFloor delta gapEpsilon)
      (bad.refinedScales C (Q.toState C delta_pos)
        gap_pos.le delta_pos) at growth
  have count_lt := separatedFactorCount_lt_stageBudget
    (gapEpsilon := gapEpsilon) N
      (bad.refinedScales C (Q.toState C delta_pos) gap_pos.le delta_pos)
      delta_pos delta_lt_one gap_pos exponent_budget
  unfold RelevantCanonicalFactorCountInvariant at hQ
  have N_pos : 1 <= N := by
    rw [← stage_eq]
    exact Q.stage_pos
  omega

/-! ## Canonical relevant invariant-bearing state space -/

/-- The recursive state consists of exactly relevant canonical data and its
separated-factor history invariant. -/
structure RelevantCanonicalCountedState
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (gapEpsilon : Real) (eta : Nat -> Real) where
  data : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta
  factorCount : RelevantCanonicalFactorCountInvariant data

namespace RelevantCanonicalCountedState

variable (C : CoherentStickyMultiscaleCover fine)
  (X : RelevantCanonicalCountedState C N gapEpsilon eta)

def toState (delta_pos : 0 < delta) :
    RelevantEnvelopeStoppingState delta N gapEpsilon eta :=
  X.data.toState C delta_pos

@[simp] theorem toState_stage (delta_pos : 0 < delta) :
    (X.toState C delta_pos).stage = X.data.stage := rfl

@[simp] theorem toState_scales (delta_pos : 0 < delta) :
    (X.toState C delta_pos).scales = X.data.scales := rfl

@[simp] theorem toState_buffered (delta_pos : 0 < delta) :
    (X.toState C delta_pos).buffered = X.data.buffered C delta_pos := rfl

end RelevantCanonicalCountedState

def relevantCanonicalCountedInitialState
    (C : CoherentStickyMultiscaleCover fine)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (stage_eq : Q.stage = 1) :
    RelevantCanonicalCountedState C N gapEpsilon eta where
  data := Q
  factorCount := relevantCanonicalFactorCountInvariant_of_stage_eq_one
    C Q stage_eq

/-- The only analytic input to the recursion: given an invariant-bearing
relevant canonical state and a literal bad split below the stage bound,
supply the two canonical child bodies and the two conditionally required
child envelope estimates. -/
def RelevantCanonicalChildSuccessor
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta) : Type _ :=
  forall (X : RelevantCanonicalCountedState C N gapEpsilon eta),
    forall _stage_lt : X.data.stage < N,
    forall bad : RelevantSelectedActualBadSplit C
      (X.toState C delta_pos),
      RelevantCanonicalChildCertificate C gap_nonneg delta_pos X.data bad

/-! ## Counting-backed bounded recursion -/

def relevantCanonicalCountingNext
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (X : RelevantCanonicalCountedState C N gapEpsilon eta) :
    Option (RelevantCanonicalCountedState C N gapEpsilon eta) := by
  classical
  by_cases hbad : Nonempty
      (RelevantSelectedActualBadSplit C (X.toState C delta_pos))
  · have stage_lt : X.data.stage < N := by
      by_contra not_lt
      have stage_eq : X.data.stage = N := by
        have := X.data.stage_le
        omega
      exact (no_relevant_bad_of_factorCountInvariant_at_bound
        C delta_pos delta_lt_one gap_pos exponent_budget X.data X.factorCount
        stage_eq) hbad
    let bad : RelevantSelectedActualBadSplit C (X.toState C delta_pos) :=
      Classical.choice hbad
    let R := successor X stage_lt bad
    exact some
      { data := R.toCanonical C gap_pos.le delta_pos X.data bad
          eta_monotone stage_lt
        factorCount := relevantCanonicalFactorCountInvariant_toCanonical
          C gap_pos.le delta_pos gap_pos eta_monotone X.data bad R stage_lt
          X.factorCount }
  · exact none

theorem relevantCanonicalCountingNext_eq_none_iff_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (X : RelevantCanonicalCountedState C N gapEpsilon eta) :
    relevantCanonicalCountingNext C delta_pos delta_lt_one gap_pos
        eta_monotone exponent_budget successor X = none <->
      Not (Nonempty
        (RelevantSelectedActualBadSplit C (X.toState C delta_pos))) := by
  classical
  simp [relevantCanonicalCountingNext]

theorem relevantCanonicalCountingNext_stage
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    {X Y : RelevantCanonicalCountedState C N gapEpsilon eta}
    (hnext : relevantCanonicalCountingNext C delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget successor X = some Y) :
    Y.data.stage = X.data.stage + 1 := by
  classical
  unfold relevantCanonicalCountingNext at hnext
  split at hnext
  next hbad =>
    have state_eq := Option.some.inj hnext
    rw [← state_eq]
    rfl
  next hbad =>
    simp at hnext

def relevantCanonicalCountingBoundedSystem
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos) :
    BoundedSuccessorSystem
      (RelevantCanonicalCountedState C N gapEpsilon eta) N where
  stage := fun X => X.data.stage
  stage_le := fun X => X.data.stage_le
  next := relevantCanonicalCountingNext C delta_pos delta_lt_one gap_pos
    eta_monotone exponent_budget successor
  stage_next := relevantCanonicalCountingNext_stage C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget successor

def relevantCanonicalCountingTerminalState
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState C N gapEpsilon eta) :
    RelevantCanonicalCountedState C N gapEpsilon eta :=
  (relevantCanonicalCountingBoundedSystem C delta_pos delta_lt_one gap_pos
    eta_monotone exponent_budget successor).terminalState initial

theorem relevantCanonicalCountingNext_terminalState_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState C N gapEpsilon eta) :
    relevantCanonicalCountingNext C delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget successor
      (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one gap_pos
        eta_monotone exponent_budget successor initial) = none := by
  exact (relevantCanonicalCountingBoundedSystem C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget successor).next_terminalState_eq_none
      initial

theorem relevantCanonicalCountingTerminalState_reachesIn
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState C N gapEpsilon eta) :
    exists steps, steps <= N - initial.data.stage /\
      (relevantCanonicalCountingBoundedSystem C delta_pos delta_lt_one gap_pos
        eta_monotone exponent_budget successor).ReachesIn steps initial
          (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget successor initial) := by
  exact (relevantCanonicalCountingBoundedSystem C delta_pos delta_lt_one
    gap_pos eta_monotone exponent_budget successor).terminalState_reachesIn
      initial

theorem relevantCanonicalCountingTerminalState_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState C N gapEpsilon eta) :
    Not (Nonempty (RelevantSelectedActualBadSplit C
      ((relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget successor initial).toState
          C delta_pos))) := by
  exact (relevantCanonicalCountingNext_eq_none_iff_no_bad C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget successor _).1
      (relevantCanonicalCountingNext_terminalState_eq_none C delta_pos
        delta_lt_one gap_pos eta_monotone exponent_budget successor initial)

/-! ## Literal terminal output and recovered-endpoint input -/

/-- For relevant states, absence of a literal bad split is still exactly the
selected actual terminal no-split predicate. -/
theorem relevant_no_bad_iff_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta) :
    Not (Nonempty (RelevantSelectedActualBadSplit C X)) <->
      forall not_all_large : Not (X.scales.AllStepsLarge gapEpsilon),
        SelectedActualTerminalNoSplit (C.toActualIntervalCovers X.scales)
          gapEpsilon eta X.stage
          (firstNonLargeStep X.scales gapEpsilon not_all_large) := by
  constructor
  · intro no_bad not_all_large
    rintro ⟨rho, rho_buffered, strict⟩
    exact no_bad ⟨{
      not_all_large := not_all_large
      rho := rho
      rho_buffered := rho_buffered
      strict := strict }⟩
  · intro terminalNoSplit
    rintro ⟨bad⟩
    exact terminalNoSplit bad.not_all_large
      ⟨bad.rho, bad.rho_buffered, bad.strict⟩

theorem relevantCanonicalCountingTerminalState_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState C N gapEpsilon eta) :
    forall not_all_large : Not
        ((relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget successor initial).data.scales.AllStepsLarge
            gapEpsilon),
      SelectedActualTerminalNoSplit
        (C.toActualIntervalCovers
          (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget successor initial).data.scales)
        gapEpsilon eta
        (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget successor initial).data.stage
        (firstNonLargeStep
          (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget successor initial).data.scales
          gapEpsilon not_all_large) := by
  exact (relevant_no_bad_iff_terminalNoSplit C _).1
    (relevantCanonicalCountingTerminalState_no_bad C delta_pos delta_lt_one
      gap_pos eta_monotone exponent_budget successor initial)

/-- The terminal relevant invariant supplies exactly the global-product bound
at the first non-large interval consumed by the recovered endpoint theorem. -/
theorem relevantCanonicalCountingTerminalState_actualGlobalProductAt_firstNonLarge_le
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState C N gapEpsilon eta)
    (not_all_large : Not
      ((relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget successor initial).data.scales.AllStepsLarge
          gapEpsilon)) :
    actualGlobalProductAt
        ((relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget successor initial).data.buffered
            C delta_pos)
        (firstNonLargeStep
          (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget successor initial).data.scales
          gapEpsilon not_all_large) <=
      requiredGlobalPowerAt
        (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget successor initial).data.scales
        eta
        (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget successor initial).data.stage
        (firstNonLargeStep
          (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget successor initial).data.scales
          gapEpsilon not_all_large) := by
  let terminal := relevantCanonicalCountingTerminalState C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget successor initial
  exact (terminal.toState C delta_pos).actualGlobalProductAt_firstNonLarge_le
    not_all_large

#print axioms relevantBadSplit_separatedFactorCount_succ_le
#print axioms relevantCanonicalFactorCountInvariant_toCanonical
#print axioms no_relevant_bad_of_factorCountInvariant_at_bound
#print axioms relevantCanonicalCountingNext_eq_none_iff_no_bad
#print axioms relevantCanonicalCountingNext_stage
#print axioms relevantCanonicalCountingNext_terminalState_eq_none
#print axioms relevantCanonicalCountingTerminalState_reachesIn
#print axioms relevantCanonicalCountingTerminalState_no_bad
#print axioms relevantCanonicalCountingTerminalState_terminalNoSplit
#print axioms relevantCanonicalCountingTerminalState_actualGlobalProductAt_firstNonLarge_le

end
end FamilyStickyScaleChainRelevantCountedStoppingDriverV2
