import FamilyStickyGrounding.FamilyStickyScaleChainBoundedRecursiveStoppingV2
import FamilyStickyGrounding.FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
import FamilyStickyGrounding.FamilyStickyScaleSequenceRefinesAtV2
import FamilyStickyGrounding.FamilyStickyScaleChainTwoParameterTerminalNoSplitV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
open FamilyStickyScaleSequenceRefinesAtV2
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
open FamilyStickyScaleChainBoundedRecursiveStoppingV2

noncomputable section

/-!
# Hierarchy-backed recursive stopping driver

This module turns the paper-shaped one-step refinement into a finite driver.
A state existentially packages its current scale depth and buffered hierarchy
depth.  Two external inputs remain explicit: a hierarchy refinement below the
stage bound, and the counting/exponent fact that no bad split remains exactly
at the bound.  Neither is manufactured by the generic recursion engine.

Classical choice selects one bad scale and the supplied refinement
certificate.  Once the two inputs are fixed, bounded termination and the
literal terminal no-split classification are theorems.
`BufferedChainFamily` currently carries abstract hierarchy data but no field
binding that hierarchy to `C`, the current scale sequence, or the original
fine family.  A concrete hierarchy--scale/fine-family realization and its
producer therefore remain outside this structural driver.

-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Dynamic hierarchy state -/

/-- A data-bearing dynamic Family7 stopping state.  Both finite depths are data:
`depth` is the current dividing-scale depth, and `chainDepth` is the depth of
the buffered hierarchy attached to each current interval.  The global
envelope inequality is maintained on every interval, so it remains valid if
insertion moves the first non-large interval to a later old coordinate. -/
structure HierarchyStoppingState
    (delta : NNReal) (N : Nat) (gapEpsilon : Real)
    (eta : Nat -> Real) where
  depth : Nat
  depth_pos : 0 < depth
  chainDepth : Nat
  scales : FiniteScaleSequence delta depth
  buffered : BufferedChainFamily depth chainDepth
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  globalEnvelope_upper : forall m : Fin depth,
    hierarchyGlobalEnvelopeAt buffered m <=
      requiredGlobalPowerAt scales eta stage m

/-! ## Literal bad split and canonical scale insertion -/

/-- The literal bad split selected at the first non-large interval.  This is
exactly the strict negation used by `SelectedActualTerminalNoSplit`; no
finite-node surrogate or prepackaged terminal conclusion occurs here. -/
structure SelectedActualBadSplit
    (C : CoherentStickyMultiscaleCover fine)
    (X : HierarchyStoppingState delta N gapEpsilon eta) where
  not_all_large : Not (X.scales.AllStepsLarge gapEpsilon)
  rho : NNReal
  rho_buffered : X.scales.IsBuffered gapEpsilon
    (firstNonLargeStep X.scales gapEpsilon not_all_large) rho
  strict :
    (C.toActualIntervalCovers X.scales).coarseValueAt
        (firstNonLargeStep X.scales gapEpsilon not_all_large) rho <
      splitThreshold X.scales eta X.stage
        (firstNonLargeStep X.scales gapEpsilon not_all_large) rho

namespace SelectedActualBadSplit

variable (C : CoherentStickyMultiscaleCover fine)
  (X : HierarchyStoppingState delta N gapEpsilon eta)
  (bad : SelectedActualBadSplit C X)

/-- The selected first non-large interval carried by a bad split. -/
def selectedStep : Fin X.depth :=
  firstNonLargeStep X.scales gapEpsilon bad.not_all_large

/-- The canonical next scale sequence inserts the literal bad radius. -/
def refinedScales (gap_nonneg : 0 <= gapEpsilon)
    (delta_pos : 0 < delta) :
    FiniteScaleSequence delta (X.depth + 1) :=
  FiniteScaleSequence.insertBufferedRadius X.scales bad.selectedStep bad.rho
    delta_pos gap_nonneg bad.rho_buffered

/-- The canonical next sequence is a lossless refinement at the bad radius. -/
theorem refinedScales_refinesAt (gap_nonneg : 0 <= gapEpsilon)
    (delta_pos : 0 < delta) :
    FiniteScaleSequence.ScaleSequenceRefinesAt X.scales bad.selectedStep
      bad.rho (bad.refinedScales C X gap_nonneg delta_pos) := by
  exact FiniteScaleSequence.insertBufferedRadius_refinesAt X.scales
    bad.selectedStep bad.rho delta_pos gap_nonneg bad.rho_buffered

end SelectedActualBadSplit

/-! ## Explicit one-step transition package -/

/-- Data required after inserting one literal bad scale.  The new scale
sequence is definitionally `SelectedActualBadSplit.refinedScales`; the input
supplies a new abstract buffered hierarchy and its envelope inequality on
every new interval.  The new stage bound follows from `X.stage < N`. -/
structure OneStepRefinementCertificate
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X) where
  newChainDepth : Nat
  newBuffered : BufferedChainFamily (X.depth + 1) newChainDepth
  globalEnvelope_upper : forall m : Fin (X.depth + 1),
    hierarchyGlobalEnvelopeAt newBuffered m <=
      requiredGlobalPowerAt
        (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1) m

namespace OneStepRefinementCertificate

variable (C : CoherentStickyMultiscaleCover fine)
  (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
  (X : HierarchyStoppingState delta N gapEpsilon eta)
  (bad : SelectedActualBadSplit C X)
  (R : OneStepRefinementCertificate C gap_nonneg delta_pos X bad)

/-- Materialize a certified below-bound refinement as the next dynamic state.
The successor-stage bound is arithmetic, rather than analytic certificate
data. -/
def toState (stage_lt : X.stage < N) :
    HierarchyStoppingState delta N gapEpsilon eta where
  depth := X.depth + 1
  depth_pos := Nat.succ_pos X.depth
  chainDepth := R.newChainDepth
  scales := bad.refinedScales C X gap_nonneg delta_pos
  buffered := R.newBuffered
  stage := X.stage + 1
  stage_pos := by omega
  stage_le := by omega
  globalEnvelope_upper := R.globalEnvelope_upper

@[simp] theorem toState_stage (stage_lt : X.stage < N) :
    (R.toState C gap_nonneg delta_pos X bad stage_lt).stage =
      X.stage + 1 := rfl

@[simp] theorem toState_scales (stage_lt : X.stage < N) :
    (R.toState C gap_nonneg delta_pos X bad stage_lt).scales =
      bad.refinedScales C X gap_nonneg delta_pos := rfl

/-- Every materialized successor retains the explicit insertion certificate. -/
theorem toState_scales_refinesAt (stage_lt : X.stage < N) :
    FiniteScaleSequence.ScaleSequenceRefinesAt X.scales bad.selectedStep
      bad.rho (R.toState C gap_nonneg delta_pos X bad stage_lt).scales := by
  exact bad.refinedScales_refinesAt C X gap_nonneg delta_pos

end OneStepRefinementCertificate

/-- The below-bound hierarchy refinement input.  For a literal bad split at
`X.stage < N`, it supplies a new abstract buffered hierarchy and its
all-interval envelope invariant.  This module does not construct that data. -/
def HierarchyAnalyticSuccessor
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta) : Type _ :=
  forall (X : HierarchyStoppingState delta N gapEpsilon eta),
    X.stage < N -> forall (bad : SelectedActualBadSplit C X),
      OneStepRefinementCertificate C gap_nonneg delta_pos X bad

/-- The separate finite-stopping seam at the last allowed stage.  In the
paper this is supplied by the counting/exponent bound on successful
refinements; it is not a consequence of recursion alone. -/
def NoBadAtStageBound
    (C : CoherentStickyMultiscaleCover fine) : Prop :=
  forall (X : HierarchyStoppingState delta N gapEpsilon eta),
    X.stage = N -> Not (Nonempty (SelectedActualBadSplit C X))

/-- The last-stage input explicitly excludes every literal bad split. -/
theorem no_bad_of_stage_eq_bound
    (C : CoherentStickyMultiscaleCover fine)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (stage_eq : X.stage = N) :
    Not (Nonempty (SelectedActualBadSplit C X)) :=
  noBadAtBound X stage_eq

/-- Select one literal bad radius when one exists.  The explicit last-stage
input first proves that the current stage is below `N`, after which the
below-bound hierarchy successor is applicable. -/
def next
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (X : HierarchyStoppingState delta N gapEpsilon eta) :
    Option (HierarchyStoppingState delta N gapEpsilon eta) := by
  classical
  by_cases hbad : Nonempty (SelectedActualBadSplit C X)
  · have stage_lt : X.stage < N := by
      have stage_le := X.stage_le
      by_contra not_lt
      have stage_eq : X.stage = N := by omega
      exact (noBadAtBound X stage_eq) hbad
    let bad := Classical.choice hbad
    exact some ((successor X stage_lt bad).toState
      C gap_nonneg delta_pos X bad stage_lt)
  · exact none

/-- The selected successor stops exactly when no literal bad split exists. -/
theorem next_eq_none_iff_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (X : HierarchyStoppingState delta N gapEpsilon eta) :
    next C gap_nonneg delta_pos successor noBadAtBound X = none <->
      Not (Nonempty (SelectedActualBadSplit C X)) := by
  classical
  simp [next]

/-- Every selected hierarchy successor raises the stage exactly once. -/
theorem stage_next
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    {X Y : HierarchyStoppingState delta N gapEpsilon eta}
    (hnext : next C gap_nonneg delta_pos successor noBadAtBound X = some Y) :
    Y.stage = X.stage + 1 := by
  classical
  unfold next at hnext
  split at hnext
  next hbad =>
    have state_eq := Option.some.inj hnext
    rw [← state_eq]
    rfl
  next hbad =>
    simp at hnext

/-- The hierarchy driver is an instance of the generic bounded successor
system.  Its stage bound is stored in each state, while exact increment comes
from the one-step certificate. -/
def boundedSystem
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C) :
    BoundedSuccessorSystem
      (HierarchyStoppingState delta N gapEpsilon eta) N where
  stage := HierarchyStoppingState.stage
  stage_le := HierarchyStoppingState.stage_le
  next := next C gap_nonneg delta_pos successor noBadAtBound
  stage_next := stage_next C gap_nonneg delta_pos successor noBadAtBound

/-- Run the hierarchy successor for exactly the remaining stage budget. -/
def terminalState
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (initial : HierarchyStoppingState delta N gapEpsilon eta) :
    HierarchyStoppingState delta N gapEpsilon eta :=
  (boundedSystem C gap_nonneg delta_pos successor noBadAtBound).terminalState initial

/-- The computed hierarchy state has no successor. -/
theorem next_terminalState_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (initial : HierarchyStoppingState delta N gapEpsilon eta) :
    next C gap_nonneg delta_pos successor noBadAtBound
      (terminalState C gap_nonneg delta_pos successor noBadAtBound initial) = none := by
  exact (boundedSystem C gap_nonneg delta_pos successor noBadAtBound).next_terminalState_eq_none
    initial

/-- The computed terminal state is reached in at most the initial remaining
stage budget. -/
theorem terminalState_reachesIn
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (initial : HierarchyStoppingState delta N gapEpsilon eta) :
    exists steps, steps <= N - initial.stage /\
      (boundedSystem C gap_nonneg delta_pos successor noBadAtBound).ReachesIn steps initial
        (terminalState C gap_nonneg delta_pos successor noBadAtBound initial) := by
  exact (boundedSystem C gap_nonneg delta_pos successor noBadAtBound).terminalState_reachesIn
    initial

/-- The hierarchy stage is monotone along the computed stopping run. -/
theorem stage_le_terminalState
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (initial : HierarchyStoppingState delta N gapEpsilon eta) :
    initial.stage <=
      (terminalState C gap_nonneg delta_pos successor noBadAtBound initial).stage := by
  exact (boundedSystem C gap_nonneg delta_pos successor noBadAtBound).stage_le_terminalState
    initial

/-! ## Exact terminal classification -/

/-- Absence of a selected actual bad split is equivalent to literal
terminal no-split at every proof of the non-all-large branch. -/
theorem no_bad_iff_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (X : HierarchyStoppingState delta N gapEpsilon eta) :
    Not (Nonempty (SelectedActualBadSplit C X)) <->
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
/-- At the last allowed stage, the separate counting input gives the literal
terminal no-split statement directly. -/
theorem terminalNoSplit_of_stage_eq_bound
    (C : CoherentStickyMultiscaleCover fine)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon)
      (N := N) (eta := eta) C)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (stage_eq : X.stage = N) :
    forall not_all_large : Not (X.scales.AllStepsLarge gapEpsilon),
      SelectedActualTerminalNoSplit (C.toActualIntervalCovers X.scales)
        gapEpsilon eta X.stage
        (firstNonLargeStep X.scales gapEpsilon not_all_large) := by
  exact (no_bad_iff_terminalNoSplit C X).1
    (no_bad_of_stage_eq_bound C noBadAtBound X stage_eq)


/-- Any state where the driver stops is exactly in the all-large branch or
carries the source paper's literal selected terminal no-split statement. -/
theorem allLarge_or_terminalNoSplit_of_next_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (hterminal : next C gap_nonneg delta_pos successor noBadAtBound X = none) :
    X.scales.AllStepsLarge gapEpsilon \/
      exists not_all_large : Not (X.scales.AllStepsLarge gapEpsilon),
        SelectedActualTerminalNoSplit (C.toActualIntervalCovers X.scales)
          gapEpsilon eta X.stage
          (firstNonLargeStep X.scales gapEpsilon not_all_large) := by
  have no_bad :=
    (next_eq_none_iff_no_bad C gap_nonneg delta_pos successor noBadAtBound X).1 hterminal
  by_cases all_large : X.scales.AllStepsLarge gapEpsilon
  · exact Or.inl all_large
  · exact Or.inr ⟨all_large,
      (no_bad_iff_terminalNoSplit C X).1 no_bad all_large⟩

/-- The bounded run therefore reaches the exact terminal dichotomy after at
most `N - initial.stage` successor steps. -/
theorem terminalState_allLarge_or_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (initial : HierarchyStoppingState delta N gapEpsilon eta) :
    let terminal := terminalState C gap_nonneg delta_pos successor noBadAtBound initial
    terminal.scales.AllStepsLarge gapEpsilon \/
      exists not_all_large : Not
          (terminal.scales.AllStepsLarge gapEpsilon),
        SelectedActualTerminalNoSplit
          (C.toActualIntervalCovers terminal.scales)
          gapEpsilon eta terminal.stage
          (firstNonLargeStep terminal.scales gapEpsilon not_all_large) := by
  exact allLarge_or_terminalNoSplit_of_next_eq_none
    C gap_nonneg delta_pos successor noBadAtBound
    (terminalState C gap_nonneg delta_pos successor noBadAtBound initial)
    (next_terminalState_eq_none C gap_nonneg delta_pos successor noBadAtBound initial)

/-! ## Optional connection to the existing V2 recovered endpoint -/

/-- At any stopped hierarchy state, its all-interval hierarchy envelope
supplies the selected global-product inequality.  Thus the no-split branch
feeds the existing two-exponent recovered endpoint without a finite-node fallback.
-/
theorem allLarge_or_twoExponentWitness_of_next_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (hterminal : next C gap_nonneg delta_pos successor noBadAtBound X = none)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta X.stage < targetExponent)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta (X.stage - 1))) :
    X.scales.AllStepsLarge gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent (recoveredProfileV2 eta X.stage targetExponent)) := by
  rcases allLarge_or_terminalNoSplit_of_next_eq_none
      C gap_nonneg delta_pos successor noBadAtBound X hterminal with
    all_large | ⟨not_all_large, terminalNoSplit⟩
  · exact Or.inl all_large
  · right
    have globalProduct : actualGlobalProductAt X.buffered
          (firstNonLargeStep X.scales gapEpsilon not_all_large) <=
        requiredGlobalPowerAt X.scales eta X.stage
          (firstNonLargeStep X.scales gapEpsilon not_all_large) := by
      exact (actualGlobalProductAt_le_hierarchyGlobalEnvelopeAt X.buffered
        (firstNonLargeStep X.scales gapEpsilon not_all_large)).trans
          (X.globalEnvelope_upper (firstNonLargeStep X.scales gapEpsilon not_all_large))
    exact
      exists_twoExponentRecoveredLiteralWitnessV2_of_globalProduct_and_terminalNoSplit
        C X.buffered X.stage X.stage_pos X.stage_le eta_monotone two_le_zero
        strict_room not_all_large globalProduct terminalNoSplit gap_pos
        delta_pos delta_le

/-- Specialization of the endpoint connector to the computed bounded terminal
state. -/
theorem terminalState_allLarge_or_twoExponentWitness
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (successor : HierarchyAnalyticSuccessor (N := N) (eta := eta) C gap_nonneg delta_pos)
    (noBadAtBound : NoBadAtStageBound (gapEpsilon := gapEpsilon) (N := N) (eta := eta) C)
    (initial : HierarchyStoppingState delta N gapEpsilon eta)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta
      (terminalState C gap_nonneg delta_pos successor noBadAtBound initial).stage <
        targetExponent)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta ((terminalState C gap_nonneg delta_pos successor noBadAtBound initial).stage - 1))) :
    let terminal := terminalState C gap_nonneg delta_pos successor noBadAtBound initial
    terminal.scales.AllStepsLarge gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta terminal.stage targetExponent)) := by
  exact allLarge_or_twoExponentWitness_of_next_eq_none
    C gap_nonneg delta_pos successor noBadAtBound
    (terminalState C gap_nonneg delta_pos successor noBadAtBound initial)
    (next_terminalState_eq_none C gap_nonneg delta_pos successor noBadAtBound initial)
    eta_monotone two_le_zero strict_room gap_pos delta_le

#print axioms SelectedActualBadSplit.refinedScales_refinesAt
#print axioms OneStepRefinementCertificate.toState_scales_refinesAt
#print axioms no_bad_of_stage_eq_bound
#print axioms terminalNoSplit_of_stage_eq_bound
#print axioms next_eq_none_iff_no_bad

#print axioms stage_next
#print axioms next_terminalState_eq_none
#print axioms terminalState_reachesIn
#print axioms terminalState_allLarge_or_terminalNoSplit
#print axioms allLarge_or_twoExponentWitness_of_next_eq_none
#print axioms terminalState_allLarge_or_twoExponentWitness

end
end FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
