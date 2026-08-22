import FamilyStickyGrounding.FamilyStickyDividingScalesFiniteStoppingV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyDividingScalesNoSplitV2

open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Sticky Kakeya: producing the terminal barrier from no further split

The first finite stopping module accepts the local terminal alternative.
Here that alternative is derived from the lower-level stopping certificate:
on a long terminal interval there is no buffered scale at which the value is
strictly below the next exponent threshold.  Negating this existential gives
the uniform lower bound at every buffered scale.

Thus neither the local barrier nor the final A/B dichotomy is assumed.
-/

/-- Failure of a strict sub-threshold witness gives a pointwise lower bound
on the entire search domain. -/
theorem lowerBound_of_no_strict_split
    {alpha : Type*} (domain : alpha -> Prop)
    (value threshold : alpha -> ENNReal)
    (hnoSplit : ¬ exists x, domain x ∧ value x < threshold x) :
    forall x, domain x -> threshold x <= value x := by
  intro x hx
  exact le_of_not_gt fun hlt => hnoSplit ⟨x, hx, hlt⟩

/-- Frostman stopping data before the no-split certificate has been converted
to the terminal barrier used by the finite dichotomy. -/
structure FrostmanNoSplitRun
    (delta : NNReal) (depth N : Nat) (epsilon : Real)
    (eta : Nat -> Real)
    (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  eta_stage_le_epsilon : eta stage <= epsilon
  fineFiberValue : Fin depth -> ENNReal
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  fineFiber_upper : forall m,
    fineFiberValue m <=
      (((S.tau m / delta : NNReal) : ENNReal) ^ eta (stage - 1))
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
    ¬ exists rho, S.IsBuffered epsilon m rho ∧
      middleValue m rho <
        (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)

namespace FrostmanNoSplitRun

variable {delta : NNReal} {depth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {S : FiniteScaleSequence delta depth}

/-- Convert a no-split terminal certificate to the local barrier expected by
the basic finite stopping run. -/
def toStoppingRun
    (R : FrostmanNoSplitRun delta depth N epsilon eta S) :
    FrostmanStoppingRun delta depth N epsilon eta S where
  stage := R.stage
  stage_pos := R.stage_pos
  stage_le := R.stage_le
  eta_monotone := R.eta_monotone
  eta_stage_le_epsilon := R.eta_stage_le_epsilon
  fineFiberValue := R.fineFiberValue
  adjacentValue := R.adjacentValue
  middleValue := R.middleValue
  fineFiber_upper := R.fineFiber_upper
  adjacent_upper := R.adjacent_upper
  terminal := by
    intro m
    by_cases hlarge : S.IsLarge epsilon m
    · exact Or.inl hlarge
    · right
      exact lowerBound_of_no_strict_split
        (S.IsBuffered epsilon m)
        (R.middleValue m)
        (fun rho =>
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta R.stage))
        (R.terminal_noSplit m hlarge)

/-- Source-shaped Frostman A dichotomy produced from no-split data. -/
theorem allLarge_or_witness
    (R : FrostmanNoSplitRun delta depth N epsilon eta S) :
    S.AllStepsLarge epsilon ∨
      Nonempty (FrostmanDividingWitness delta N epsilon eta) :=
  R.toStoppingRun.allLarge_or_witness

/-- Literal at-every-scale Frostman wrapper for the all-large branch. -/
theorem frostmanAtEveryScale_or_witness
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (M : StickyMultiscaleCover fine) (error : ENNReal)
    (R : FrostmanNoSplitRun delta depth N epsilon eta S)
    (hall : S.AllStepsLarge epsilon ->
      M.IsFrostmanAtEveryScale error) :
    M.IsFrostmanAtEveryScale error ∨
      Nonempty (FrostmanDividingWitness delta N epsilon eta) :=
  R.toStoppingRun.frostmanAtEveryScale_or_witness M error hall

end FrostmanNoSplitRun

/-- Katz--Tao stopping data with the Part (B) threshold orientation. -/
structure KatzTaoNoSplitRun
    (delta : NNReal) (depth N : Nat) (epsilon : Real)
    (eta : Nat -> Real)
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
  terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
    ¬ exists rho, S.IsBuffered epsilon m rho ∧
      middleValue m rho <
        (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage)

namespace KatzTaoNoSplitRun

variable {delta : NNReal} {depth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {S : FiniteScaleSequence delta depth}

/-- Convert the Part (B) no-split certificate to a terminal barrier. -/
def toStoppingRun
    (R : KatzTaoNoSplitRun delta depth N epsilon eta S) :
    KatzTaoStoppingRun delta depth N epsilon eta S where
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
        (R.middleValue m)
        (fun rho =>
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta R.stage))
        (R.terminal_noSplit m hlarge)

/-- Source-shaped Katz--Tao B dichotomy produced from no-split data. -/
theorem allLarge_or_witness
    (R : KatzTaoNoSplitRun delta depth N epsilon eta S) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) :=
  R.toStoppingRun.allLarge_or_witness

/-- Literal at-every-scale Katz--Tao wrapper for the all-large branch. -/
theorem katzTaoAtEveryScale_or_witness
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (M : StickyMultiscaleCover fine) (error : ENNReal)
    (R : KatzTaoNoSplitRun delta depth N epsilon eta S)
    (hall : S.AllStepsLarge epsilon ->
      M.IsKatzTaoAtEveryScale error) :
    M.IsKatzTaoAtEveryScale error ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) :=
  R.toStoppingRun.katzTaoAtEveryScale_or_witness M error hall

end KatzTaoNoSplitRun

#print axioms lowerBound_of_no_strict_split
#print axioms FrostmanNoSplitRun.allLarge_or_witness
#print axioms FrostmanNoSplitRun.frostmanAtEveryScale_or_witness
#print axioms KatzTaoNoSplitRun.allLarge_or_witness
#print axioms KatzTaoNoSplitRun.katzTaoAtEveryScale_or_witness

end

end FamilyStickyDividingScalesNoSplitV2
