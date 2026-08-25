import FamilyStickyGrounding.FamilyStickyScaleChainRelevantThetaCapInvariantV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainUniformAutomaticThetaThresholdV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2
open FamilyStickyScaleChainRelevantThetaCapInvariantV2

noncomputable section

/-!
# A uniform automatic child-theta threshold

The automatic canonical child estimate at recursion stage `s` asks for
`theta <= automaticOneStepSmallThetaThreshold n (eta s)`.  The recursive
minimum below fixes one cap before the run and makes it valid for every
stage `s < N`.  This is solely the child-theta cap; it does not duplicate the
independent adjacent-endpoint delta threshold.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real} {cap : NNReal}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Recursive minimum over stages `0, ..., N - 1` -/

/-- Minimum of the automatic one-step theta thresholds at profile indices
`0, ..., N - 1`.  The value at `N = 0` is the harmless positive unit. -/
def uniformAutomaticThetaThreshold
    (n : Nat) (eta : Nat -> Real) : Nat -> NNReal
  | 0 => 1
  | N + 1 =>
      min (uniformAutomaticThetaThreshold n eta N)
        (automaticOneStepSmallThetaThreshold n (eta N))

@[simp] theorem uniformAutomaticThetaThreshold_zero
    (n : Nat) (eta : Nat -> Real) :
    uniformAutomaticThetaThreshold n eta 0 = 1 :=
  rfl

@[simp] theorem uniformAutomaticThetaThreshold_succ
    (n : Nat) (eta : Nat -> Real) (N : Nat) :
    uniformAutomaticThetaThreshold n eta (N + 1) =
      min (uniformAutomaticThetaThreshold n eta N)
        (automaticOneStepSmallThetaThreshold n (eta N)) :=
  rfl

/-- A finite minimum of the explicit positive thresholds stays positive. -/
theorem uniformAutomaticThetaThreshold_pos
    (n : Nat) (eta : Nat -> Real) (N : Nat) :
    0 < uniformAutomaticThetaThreshold n eta N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [uniformAutomaticThetaThreshold_succ, lt_min_iff]
      exact ⟨ih, automaticOneStepSmallThetaThreshold_pos n (eta N)⟩

/-- Projection of the uniform minimum to every automatic threshold included
in its stage window. -/
theorem uniformAutomaticThetaThreshold_le_stage
    (n : Nat) (eta : Nat -> Real)
    (N s : Nat) (stage_lt : s < N) :
    uniformAutomaticThetaThreshold n eta N <=
      automaticOneStepSmallThetaThreshold n (eta s) := by
  induction N generalizing s with
  | zero => omega
  | succ N ih =>
      rw [uniformAutomaticThetaThreshold_succ]
      by_cases hsN : s = N
      · subst s
        exact min_le_right _ _
      · have stage_lt_previous : s < N := by omega
        exact (min_le_left _ _).trans (ih s stage_lt_previous)

/-! ## Uniform profile room -/

/-- Monotonicity propagates a strict profile gap at zero to every stage. -/
theorem two_lt_eta_of_monotone_of_two_lt_zero
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (s : Nat) :
    2 < eta s :=
  two_lt_eta_zero.trans_le (eta_monotone (Nat.zero_le s))

/-! ## Numerical package for cap-bearing recursion -/

/-- Uniform numerical conditions for a chosen non-large theta cap.  The cap
may equal the recursive minimum, or be any smaller positive scale selected
by an upstream construction. -/
structure UniformAutomaticThetaCapNumerics
    (n : Nat) (eta : Nat -> Real) (N : Nat) (cap : NNReal) : Prop where
  eta_monotone : Monotone eta
  two_lt_eta_zero : 2 < eta 0
  cap_le_uniform : cap <= uniformAutomaticThetaThreshold n eta N

namespace UniformAutomaticThetaCapNumerics


/-- Every stage has the strict profile room required by the automatic child
estimate. -/
theorem profile_gt_two
    (numerics : UniformAutomaticThetaCapNumerics
      (Fintype.card iota) eta N cap)
    (s : Nat) :
    2 < eta s :=
  two_lt_eta_of_monotone_of_two_lt_zero numerics.eta_monotone
    numerics.two_lt_eta_zero s

/-- At every below-bound stage, the chosen cap lies below that stage's
automatic one-step threshold. -/
theorem cap_le_threshold
    (numerics : UniformAutomaticThetaCapNumerics
      (Fintype.card iota) eta N cap)
    (s : Nat) (stage_lt : s < N) :
    cap <= automaticOneStepSmallThetaThreshold (Fintype.card iota)
      (eta s) :=
  numerics.cap_le_uniform.trans
    (uniformAutomaticThetaThreshold_le_stage
      (Fintype.card iota) eta N s stage_lt)

/-- The uniform package is exactly the stage window consumed by the
cap-based relevant successor. -/
theorem toRelevantThetaCapStageWindow
    (numerics : UniformAutomaticThetaCapNumerics
      (Fintype.card iota) eta N cap) :
    RelevantThetaCapStageWindow N eta iota cap :=
  fun s _stage_pos stage_lt =>
    ⟨numerics.profile_gt_two s,
      numerics.cap_le_threshold s stage_lt⟩

end UniformAutomaticThetaCapNumerics

/-- Canonical numerical package obtained by choosing the recursive minimum
itself as the cap. -/
theorem uniformAutomaticThetaCapNumerics
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0) :
    UniformAutomaticThetaCapNumerics n eta N
      (uniformAutomaticThetaThreshold n eta N) where
  eta_monotone := eta_monotone
  two_lt_eta_zero := two_lt_eta_zero
  cap_le_uniform := le_rfl

/-! ## Direct adapters to the cap-bearing successor -/

/-- A statewise non-large cap plus the uniform numerical package constructs
the exact child successor consumed by the relevant counted driver. -/
def relevantCanonicalChildSuccessor_of_uniformAutomaticThetaCap
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (cap : NNReal)
    (statewiseCap : RelevantCanonicalStatewiseThetaCap
      C N gapEpsilon eta cap)
    (numerics : UniformAutomaticThetaCapNumerics
      (Fintype.card iota) eta N cap) :
    RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos :=
  relevantCanonicalChildSuccessor_of_nonLargeThetaCap C gap_nonneg
    delta_pos cap statewiseCap numerics.toRelevantThetaCapStageWindow

/-- Specialization in which the pre-run cap is the recursive uniform
threshold itself. -/
def relevantCanonicalChildSuccessor_of_uniformAutomaticThetaThreshold
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (statewiseCap : RelevantCanonicalStatewiseThetaCap C N gapEpsilon eta
      (uniformAutomaticThetaThreshold (Fintype.card iota) eta N)) :
    RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos :=
  relevantCanonicalChildSuccessor_of_uniformAutomaticThetaCap C gap_nonneg
    delta_pos (uniformAutomaticThetaThreshold (Fintype.card iota) eta N)
    statewiseCap
    (uniformAutomaticThetaCapNumerics (Fintype.card iota) eta N
      eta_monotone two_lt_eta_zero)

#print axioms uniformAutomaticThetaThreshold_pos
#print axioms uniformAutomaticThetaThreshold_le_stage
#print axioms two_lt_eta_of_monotone_of_two_lt_zero
#print axioms UniformAutomaticThetaCapNumerics.profile_gt_two
#print axioms UniformAutomaticThetaCapNumerics.cap_le_threshold
#print axioms UniformAutomaticThetaCapNumerics.toRelevantThetaCapStageWindow
#print axioms uniformAutomaticThetaCapNumerics
#print axioms relevantCanonicalChildSuccessor_of_uniformAutomaticThetaCap
#print axioms relevantCanonicalChildSuccessor_of_uniformAutomaticThetaThreshold

end
end FamilyStickyScaleChainUniformAutomaticThetaThresholdV2
