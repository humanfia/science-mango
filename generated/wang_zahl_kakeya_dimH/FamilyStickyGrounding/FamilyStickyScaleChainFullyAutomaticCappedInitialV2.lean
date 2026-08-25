import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import FamilyStickyGrounding.FamilyStickyScaleChainUniformAutomaticThetaThresholdV2
import FamilyStickyGrounding.FamilyStickyScaleChainRelevantThetaCapCountedDriverV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticCappedInitialV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainRelevantThetaCapInvariantV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainUniformAutomaticThetaThresholdV2
open FamilyStickyScaleChainRelevantThetaCapCountedDriverV2

noncomputable section

/-!
# Fully automatic capped initial state

Fix the non-large endpoint cap to be the finite minimum of all automatic
one-step theta thresholds before stage `N`.  One seed delta threshold then
constructs the literal depth-two chain `1, cap, delta`; its top interval is
large and its lower interval has endpoint `cap`.

The final package contains the cap, seed, automatic-body cap-bearing counted
initial state, and the complete stage window.  It accepts no successor,
child certificate, or statewise cap callback.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## The single initial delta threshold -/

/-- The cap used throughout the fully automatic recursion. -/
def fullyAutomaticThetaCap
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) : NNReal :=
  uniformAutomaticThetaThreshold (Fintype.card iota) eta N

/-- One seed threshold simultaneously gives `delta <= cap` and
`delta ^ gapEpsilon <= cap`.  The independent adjacent-endpoint threshold
can be intersected with this one only in the final recovered-endpoint
module. -/
def fullyAutomaticCappedInitialDeltaThreshold
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) : NNReal :=
  cappedSeedDeltaThreshold (fullyAutomaticThetaCap iota eta N) gapEpsilon

theorem fullyAutomaticThetaCap_pos
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) :
    0 < fullyAutomaticThetaCap iota eta N := by
  exact uniformAutomaticThetaThreshold_pos (Fintype.card iota) eta N

/-- Once the stage window is nonempty, the uniform cap is at most the
stage-zero automatic threshold and hence at most one half. -/
theorem fullyAutomaticThetaCap_le_half
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) {N : Nat} (N_pos : 1 <= N) :
    fullyAutomaticThetaCap iota eta N <= (2 : NNReal)⁻¹ := by
  calc
    fullyAutomaticThetaCap iota eta N <=
        automaticOneStepSmallThetaThreshold (Fintype.card iota) (eta 0) :=
      uniformAutomaticThetaThreshold_le_stage
        (Fintype.card iota) eta N 0 N_pos
    _ <= (2 : NNReal)⁻¹ := min_le_left _ _

theorem fullyAutomaticThetaCap_le_one
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) {N : Nat} (N_pos : 1 <= N) :
    fullyAutomaticThetaCap iota eta N <= 1 :=
  (fullyAutomaticThetaCap_le_half iota eta N_pos).trans (by norm_num)

theorem fullyAutomaticCappedInitialDeltaThreshold_pos
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    0 < fullyAutomaticCappedInitialDeltaThreshold
      iota eta N gapEpsilon := by
  exact cappedSeedDeltaThreshold_pos
    (fullyAutomaticThetaCap_pos iota eta N) gapEpsilon

theorem fullyAutomaticCappedInitialDeltaThreshold_le_one
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) {N : Nat} (N_pos : 1 <= N)
    (gapEpsilon : Real) :
    fullyAutomaticCappedInitialDeltaThreshold iota eta N gapEpsilon <= 1 := by
  exact cappedSeedDeltaThreshold_le_one
    (fullyAutomaticThetaCap_le_one iota eta N_pos) gapEpsilon

/-! ## Uniform stage window for the cap-bearing driver -/

/-- The chosen recursive minimum supplies exactly the stage-window type of
the cap-bearing counted driver. -/
theorem fullyAutomaticThetaCapStageWindow
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0) :
    FamilyStickyScaleChainRelevantThetaCapCountedDriverV2.RelevantThetaCapStageWindow
      N eta iota (fullyAutomaticThetaCap iota eta N) := by
  intro s _stage_pos stage_lt
  exact
    ⟨two_lt_eta_of_monotone_of_two_lt_zero eta_monotone
        two_lt_eta_zero s,
      uniformAutomaticThetaThreshold_le_stage
        (Fintype.card iota) eta N s stage_lt⟩

/-! ## One direct package -/

/-- All data needed to start the automatic cap-bearing counted recursion. -/
structure FullyAutomaticCappedInitialPackage
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (gapEpsilon : Real) (eta : Nat -> Real) where
  cap : NNReal
  cap_eq : cap = fullyAutomaticThetaCap iota eta N
  seed : FiniteScaleSequence delta 2
  initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap
  initial_scales_heq_seed : HEq initial.counted.data.scales seed
  stageWindow :
    FamilyStickyScaleChainRelevantThetaCapCountedDriverV2.RelevantThetaCapStageWindow
      N eta iota cap

/-- The uniform cap, capped depth-two seed, automatic terminal bodies, and
uniform stage window are constructed in one call. -/
def fullyAutomaticCappedInitialPackage
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (N_pos : 1 <= N)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= fullyAutomaticCappedInitialDeltaThreshold
      iota eta N gapEpsilon) :
    FullyAutomaticCappedInitialPackage C N gapEpsilon eta := by
  let cap : NNReal := fullyAutomaticThetaCap iota eta N
  have cap_pos : 0 < cap := fullyAutomaticThetaCap_pos iota eta N
  have cap_le_one : cap <= 1 :=
    fullyAutomaticThetaCap_le_one iota eta N_pos
  let seed : FiniteScaleSequence delta 2 :=
    cappedSeedScaleSequenceOfThresholdPos cap_pos cap_le_one gap_pos delta_le
  have seed_cap : NonLargeThetaCap seed gapEpsilon cap := by
    exact cappedSeedScaleSequenceOfThresholdPos_nonLargeThetaCap
      cap_pos cap_le_one gap_pos delta_le
  have cap_le_stage_zero : cap <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota) (eta 0) :=
    uniformAutomaticThetaThreshold_le_stage
      (Fintype.card iota) eta N 0 N_pos
  let initial : RelevantThetaCappedCountedState
      C N gapEpsilon eta cap :=
    automaticRelevantThetaCappedCountedInitialState C seed (by omega)
      fine_refined_nonempty delta_pos N_pos cap seed_cap two_lt_eta_zero
      cap_le_stage_zero
  refine {
    cap := cap
    cap_eq := rfl
    seed := seed
    initial := initial
    initial_scales_heq_seed := ?_
    stageWindow := ?_ }
  · rfl
  · exact fullyAutomaticThetaCapStageWindow iota eta N eta_monotone
      two_lt_eta_zero

@[simp] theorem fullyAutomaticCappedInitialPackage_cap
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (N_pos : 1 <= N)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= fullyAutomaticCappedInitialDeltaThreshold
      iota eta N gapEpsilon) :
    (fullyAutomaticCappedInitialPackage C delta_pos gap_pos N_pos
      eta_monotone two_lt_eta_zero fine_refined_nonempty delta_le).cap =
        fullyAutomaticThetaCap iota eta N := by
  rfl

#print axioms fullyAutomaticThetaCap_pos
#print axioms fullyAutomaticThetaCap_le_half
#print axioms fullyAutomaticThetaCap_le_one
#print axioms fullyAutomaticCappedInitialDeltaThreshold_pos
#print axioms fullyAutomaticCappedInitialDeltaThreshold_le_one
#print axioms fullyAutomaticThetaCapStageWindow
#print axioms fullyAutomaticCappedInitialPackage
#print axioms fullyAutomaticCappedInitialPackage_cap

end
end FamilyStickyScaleChainFullyAutomaticCappedInitialV2
