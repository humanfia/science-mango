import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import FamilyStickyGrounding.FamilyStickyScaleChainFixedLocalCardCountedDriverV2

/-!
# A normalized LongCore retaining its selected local-card certificate

`NormalizedLongIntervalCoreWitness` deliberately keeps only the fields used
by the existing middle-scale consumers.  In particular, the generic finite
selector forgets the proof that its selected interval is non-large.  That is
too weak for the selected-stage local-card bridge, which must query the
cardinality bound at exactly the same interval.

This module adds the minimal non-global wrapper needed by that bridge.  It
stores one established LongCore witness, non-largeness at that witness's own
index, and a single local-card bound at the same index.  It does not store a
uniform `NonLargeLocalCardBudget`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

namespace Family8LocalCardRetainedNormalizedLongCoreWitnessV1

open Submission.Kakeya.Uniformity
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedLongIntervalCoreConsumerV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainFixedLocalCardCountedDriverV2
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainLocalCardBudgetInvariantV2

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The smallest wrapper that retains the selected-stage data needed by the
local-card X producer.  All four fields refer definitionally to `core.m`; no
second interval is selected. -/
structure LocalCardRetainedNormalizedLongCoreWitness
    (fine : UniformTubeFamily delta iota)
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (epsilon : Real) (eta : Nat -> Real)
    (S : FiniteScaleSequence delta depth) where
  core : NormalizedLongIntervalCoreWitness fine C N epsilon eta S
  not_large : Not (S.IsLarge epsilon core.m)
  n : Nat
  local_card_le : adjacentIntervalActiveFineCard C S core.m <= n

namespace LocalCardRetainedNormalizedLongCoreWitness

variable {C : CoherentStickyMultiscaleCover fine}
  {S : FiniteScaleSequence delta depth}

/-- Direct constructor when the caller already has the two facts at the
LongCore's literal selected index. -/
def ofCore
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hnot : Not (S.IsLarge epsilon W.m))
    (n : Nat)
    (hlocal : adjacentIntervalActiveFineCard C S W.m <= n) :
    LocalCardRetainedNormalizedLongCoreWitness
      fine C N epsilon eta S where
  core := W
  not_large := hnot
  n := n
  local_card_le := hlocal

/-- Query a uniform budget only once, at the LongCore's own selected index,
and retain the resulting pointwise certificate. -/
def ofCoreAndBudget
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hnot : Not (S.IsLarge epsilon W.m))
    (n : Nat)
    (hbudget : NonLargeLocalCardBudget C S epsilon n) :
    LocalCardRetainedNormalizedLongCoreWitness
      fine C N epsilon eta S :=
  ofCore W hnot n (hbudget W.m hnot)

/-- Build the core and its local-card certificate at the literal
`firstNonLargeStep` of a fixed-local-card counted state.  The core index is
set to this `m` during construction, so the non-large and cardinality fields
are definitionally about the same index; there is no re-selection or
equality-transport premise.

The normalized middle barrier remains explicit because the fixed-local-card
state controls the sticky envelope, not `normalizedFiberCFValueAt`. -/
noncomputable def ofFixedLocalCardCountedStateFirstNonLargeStep
    {cap : NNReal} {n : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (X : RelevantFixedLocalCardCountedState
      C N epsilon eta cap n)
    (hNotAll : Not (X.counted.data.scales.AllStepsLarge epsilon))
    (hMiddle :
      let m := firstNonLargeStep
        X.counted.data.scales epsilon hNotAll
      forall rho : NNReal,
        X.counted.data.scales.IsBuffered epsilon m rho ->
          (((rho / X.counted.data.scales.tau m : NNReal) : ENNReal) ^
              eta X.counted.data.stage) <=
            normalizedFiberCFValueAt
              C X.counted.data.scales m rho) :
    LocalCardRetainedNormalizedLongCoreWitness
      fine C N epsilon eta X.counted.data.scales := by
  let m := firstNonLargeStep X.counted.data.scales epsilon hNotAll
  have hmNotLarge : Not
      (X.counted.data.scales.IsLarge epsilon m) :=
    firstNonLargeStep_not_large X.counted.data.scales epsilon hNotAll
  let W : NormalizedLongIntervalCoreWitness
      fine C N epsilon eta X.counted.data.scales := {
    m := m
    stage := X.counted.data.stage
    stage_pos := X.counted.data.stage_pos
    stage_le := X.counted.data.stage_le
    long := firstNonLargeStep_isLong
      X.counted.data.scales epsilon hNotAll
    middle_lower := by
      simpa only [m] using hMiddle }
  exact ofCore W
    (by simpa only [W] using hmNotLarge) n
    (by
      simpa only [W] using X.localCardBudget m hmNotLarge)

#print axioms LocalCardRetainedNormalizedLongCoreWitness
#print axioms ofCore
#print axioms ofCoreAndBudget
#print axioms ofFixedLocalCardCountedStateFirstNonLargeStep

end LocalCardRetainedNormalizedLongCoreWitness

end
end Family8LocalCardRetainedNormalizedLongCoreWitnessV1
