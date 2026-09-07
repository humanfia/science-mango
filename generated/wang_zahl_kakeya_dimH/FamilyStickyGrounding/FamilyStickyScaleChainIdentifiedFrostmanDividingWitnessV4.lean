import FamilyStickyGrounding.FamilyStickyScaleChainCoherentIntervalProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesNoSplitV2
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-!
# An identified Frostman dividing witness

The legacy `FrostmanDividingWitness` erases the selected finite interval and
therefore also erases the fact that its middle value was a literal coherent
interval-cover `fiberDeltaMax`.  Also,
`ActualIntervalCovers.toFrostmanNoSplitRun` accepts an arbitrary fine value,
because `ActualIntervalCovers` no longer retains the original delta-family.

This successor retains the coherent global cover and the selected node.  Its
fine value is definitionally the global `delta -> tau_m` fiber concentration;
its middle value is definitionally the actual `tau_m -> rho` fiber
concentration.  No value-identification callback is stored or assumed.
-/

/-- A long Frostman interval with its selected node and actual covers still
identified.  The value functions are derived, not stored as structure
fields. -/
structure IdentifiedFrostmanDividingWitness
    {delta : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (C : CoherentStickyMultiscaleCover fine)
    {depth : Nat} (N : Nat) (epsilon : Real) (eta : Nat -> Real)
    (S : FiniteScaleSequence delta depth) where
  m : Fin depth
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  long : S.IsLong epsilon m
  fineFiber_upper :
    StickyScaleCover.fiberDeltaMax
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
      (((S.tau m / delta : NNReal) : ENNReal) ^ eta (stage - 1))
  adjacent_upper :
    (C.toActualIntervalCovers S).adjacentFiberValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  middle_lower : forall rho, S.IsBuffered epsilon m rho ->
    (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
      (C.toActualIntervalCovers S).fiberValueAt m rho

namespace IdentifiedFrostmanDividingWitness

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

/-- Forget only the interval identity, recovering the legacy public witness.
All three values are fixed by the coherent cover. -/
def toFrostmanDividingWitness
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S) :
    FrostmanDividingWitness delta N epsilon eta where
  tau := S.tau W.m
  theta := S.theta W.m
  stage := W.stage
  stage_pos := W.stage_pos
  stage_le := W.stage_le
  delta_le_tau := S.delta_le_tau W.m
  tau_le_theta := S.tau_le_theta W.m
  theta_le_one := S.theta_le_one W.m
  long := W.long
  fineFiberValue :=
    StickyScaleCover.fiberDeltaMax
      (C.base.cover (S.tau W.m) (S.delta_le_tau W.m)
        ((S.tau_le_theta W.m).trans (S.theta_le_one W.m)))
  adjacentValue :=
    (C.toActualIntervalCovers S).adjacentFiberValue W.m
  middleValue :=
    (C.toActualIntervalCovers S).fiberValueAt W.m
  fineFiber_upper := W.fineFiber_upper
  adjacent_upper := W.adjacent_upper
  middle_lower := by
    intro rho hlower hupper
    exact W.middle_lower rho ⟨hlower, hupper⟩

@[simp] theorem toFrostmanDividingWitness_tau
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S) :
    W.toFrostmanDividingWitness.tau = S.tau W.m := by
  rfl

@[simp] theorem toFrostmanDividingWitness_theta
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S) :
    W.toFrostmanDividingWitness.theta = S.theta W.m := by
  rfl

@[simp] theorem toFrostmanDividingWitness_stage
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S) :
    W.toFrostmanDividingWitness.stage = W.stage := by
  rfl

/-- The legacy witness's fine value is the literal global
`delta -> tau_m` fiber concentration. -/
@[simp] theorem toFrostmanDividingWitness_fineFiberValue
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S) :
    W.toFrostmanDividingWitness.fineFiberValue =
      StickyScaleCover.fiberDeltaMax
        (C.base.cover (S.tau W.m) (S.delta_le_tau W.m)
          ((S.tau_le_theta W.m).trans (S.theta_le_one W.m))) := by
  rfl

/-- The adjacent value is the literal coherent `tau_m -> theta_m` fiber
concentration. -/
theorem toFrostmanDividingWitness_adjacentValue
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S) :
    W.toFrostmanDividingWitness.adjacentValue =
      StickyScaleCover.fiberDeltaMax
        (C.intervalScaleCover (S.tau W.m) (S.theta W.m)
          (S.delta_le_tau W.m) (S.tau_le_theta W.m)
          (S.theta_le_one W.m)) := by
  exact C.toActualIntervalCovers_adjacentFiberValue_eq S W.m

/-- At every legal selected scale, the middle value is the literal coherent
`tau_m -> rho` fiber concentration. -/
theorem toFrostmanDividingWitness_middleValue
    (W : IdentifiedFrostmanDividingWitness fine C N epsilon eta S)
    (rho : NNReal) (htau : S.tau W.m <= rho) (hrho : rho <= 1) :
    W.toFrostmanDividingWitness.middleValue rho =
      StickyScaleCover.fiberDeltaMax
        (C.intervalScaleCover (S.tau W.m) rho
          (S.delta_le_tau W.m) htau hrho) := by
  change (C.toActualIntervalCovers S).fiberValueAt W.m rho = _
  rw [(C.toActualIntervalCovers S).fiberValueAt_eq W.m rho htau hrho]
  rfl

end IdentifiedFrostmanDividingWitness

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

/-- Actual coherent Frostman no-split data yield either the all-large branch
or a selected interval whose fine and middle values remain the literal
global and interval-cover `fiberDeltaMax` values.

The proof repeats the final finite selection, since the legacy output has
already erased the selected `m`. -/
theorem allLarge_or_identifiedFrostmanDividingWitness
    (C : CoherentStickyMultiscaleCover fine)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (fineFiber_upper : forall m,
      StickyScaleCover.fiberDeltaMax
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (stage - 1)))
    (adjacent_upper : forall m,
      (C.toActualIntervalCovers S).adjacentFiberValue m <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1)))
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ ∃ rho, S.IsBuffered epsilon m rho ∧
        (C.toActualIntervalCovers S).fiberValueAt m rho <
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) :
    S.AllStepsLarge epsilon ∨
      Nonempty
        (IdentifiedFrostmanDividingWitness fine C N epsilon eta S) := by
  let A := C.toActualIntervalCovers S
  let R : FrostmanNoSplitRun delta depth N epsilon eta S :=
    A.toFrostmanNoSplitRun stage stage_pos stage_le eta_monotone
      eta_stage_le_epsilon
      (fun m => StickyScaleCover.fiberDeltaMax
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))))
      fineFiber_upper adjacent_upper terminal_noSplit
  let barrier : Fin depth -> Prop := fun m =>
    forall rho, S.IsBuffered epsilon m rho ->
      (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
        A.fiberValueAt m rho
  have hterminal : forall m, S.IsLarge epsilon m ∨ barrier m := by
    intro m
    by_cases hlarge : S.IsLarge epsilon m
    · exact Or.inl hlarge
    · right
      exact lowerBound_of_no_strict_split
        (S.IsBuffered epsilon m)
        (A.fiberValueAt m)
        (fun rho =>
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage))
        (terminal_noSplit m hlarge)
  rcases S.allStepsLarge_or_exists_long epsilon barrier hterminal with
    hall | ⟨m, hlong, hmiddle⟩
  · exact Or.inl hall
  · exact Or.inr ⟨{
      m := m
      stage := R.stage
      stage_pos := R.stage_pos
      stage_le := R.stage_le
      long := hlong
      fineFiber_upper := R.fineFiber_upper m
      adjacent_upper := R.adjacent_upper m
      middle_lower := hmiddle }⟩

#print axioms allLarge_or_identifiedFrostmanDividingWitness

end CoherentStickyMultiscaleCover

#print axioms IdentifiedFrostmanDividingWitness.toFrostmanDividingWitness
#print axioms
  IdentifiedFrostmanDividingWitness.toFrostmanDividingWitness_fineFiberValue
#print axioms
  IdentifiedFrostmanDividingWitness.toFrostmanDividingWitness_adjacentValue
#print axioms
  IdentifiedFrostmanDividingWitness.toFrostmanDividingWitness_middleValue

end
end FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
