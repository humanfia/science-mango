import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import FamilyStickyGrounding.FamilyStickyScaleChainUniformAutomaticThetaThresholdV2
import FamilyStickyGrounding.FamilyStickyScaleChainRelevantCountedUniformThresholdEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticDeltaThresholdV2

open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainUniformAutomaticThetaThresholdV2
open FamilyStickyScaleChainRelevantCountedUniformThresholdEndpointV2
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1

noncomputable section

/-!
# One precomputed delta threshold for the automatic Family 7 run

The automatic non-large-theta cap is fixed before the recursion as the
finite minimum of all child thresholds through stage `N`.  The total delta
threshold is the minimum of exactly the two independent constraints:

* the capped-seed threshold, which gives both `delta <= cap` and
  `delta ^ gapEpsilon <= cap`; and
* the uniform first-non-large adjacent-card threshold used by the recovered
  endpoint.

Thus one hypothesis `delta <= fullyAutomaticDeltaThreshold ...` supplies
all delta upper bounds needed by the seed and endpoint APIs.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota]

/-! ## The cap and the single total threshold -/

/-- The pre-run non-large-theta cap: the uniform minimum of the automatic
child thresholds at stages `0, ..., N - 1`. -/
def fullyAutomaticDeltaThetaCap
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) : NNReal :=
  uniformAutomaticThetaThreshold (Fintype.card iota) eta N

/-- The intersection of the capped-seed and uniform adjacent-card delta
constraints.  No extra `min 1` is needed: the seed factor is already at
most the automatic cap, and that cap is at most one. -/
def fullyAutomaticDeltaThreshold
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) : NNReal :=
  min
    (cappedSeedDeltaThreshold
      (fullyAutomaticDeltaThetaCap iota eta N) gapEpsilon)
    (uniformFirstNonLargeAdjacentCardThreshold
      iota gapEpsilon eta N)

@[simp] theorem fullyAutomaticDeltaThetaCap_eq
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) :
    fullyAutomaticDeltaThetaCap iota eta N =
      uniformAutomaticThetaThreshold (Fintype.card iota) eta N :=
  rfl

theorem fullyAutomaticDeltaThetaCap_pos
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) :
    0 < fullyAutomaticDeltaThetaCap iota eta N := by
  exact uniformAutomaticThetaThreshold_pos (Fintype.card iota) eta N

/-- The uniform child-threshold cap is at most one, including the harmless
`N = 0` value where it is exactly one. -/
theorem fullyAutomaticDeltaThetaCap_le_one
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) :
    fullyAutomaticDeltaThetaCap iota eta N <= 1 := by
  change uniformAutomaticThetaThreshold (Fintype.card iota) eta N <= 1
  induction N with
  | zero => simp
  | succ n ih =>
      calc
        uniformAutomaticThetaThreshold (Fintype.card iota) eta (n + 1) =
            min (uniformAutomaticThetaThreshold (Fintype.card iota) eta n)
              (FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2.automaticOneStepSmallThetaThreshold
                (Fintype.card iota) (eta n)) := rfl
        _ <= uniformAutomaticThetaThreshold (Fintype.card iota) eta n :=
          min_le_left _ _
        _ <= 1 := ih

/-- Both factors in the total finite minimum are strictly positive. -/
theorem fullyAutomaticDeltaThreshold_pos
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    0 < fullyAutomaticDeltaThreshold iota eta N gapEpsilon := by
  rw [fullyAutomaticDeltaThreshold, lt_min_iff]
  exact
    ⟨cappedSeedDeltaThreshold_pos
        (fullyAutomaticDeltaThetaCap_pos iota eta N) gapEpsilon,
      uniformFirstNonLargeAdjacentCardThreshold_pos
        iota gapEpsilon eta N⟩

theorem fullyAutomaticDeltaThreshold_le_seed
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    fullyAutomaticDeltaThreshold iota eta N gapEpsilon <=
      cappedSeedDeltaThreshold
        (fullyAutomaticDeltaThetaCap iota eta N) gapEpsilon := by
  exact min_le_left _ _

theorem fullyAutomaticDeltaThreshold_le_uniformAdjacent
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    fullyAutomaticDeltaThreshold iota eta N gapEpsilon <=
      uniformFirstNonLargeAdjacentCardThreshold
        iota gapEpsilon eta N := by
  exact min_le_right _ _

theorem fullyAutomaticDeltaThreshold_le_cap
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    fullyAutomaticDeltaThreshold iota eta N gapEpsilon <=
      fullyAutomaticDeltaThetaCap iota eta N := by
  exact (fullyAutomaticDeltaThreshold_le_seed iota eta N gapEpsilon).trans
    (cappedSeedDeltaThreshold_le_cap
      (fullyAutomaticDeltaThetaCap iota eta N) gapEpsilon)

theorem fullyAutomaticDeltaThreshold_le_one
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    fullyAutomaticDeltaThreshold iota eta N gapEpsilon <= 1 := by
  exact (fullyAutomaticDeltaThreshold_le_cap iota eta N gapEpsilon).trans
    (fullyAutomaticDeltaThetaCap_le_one iota eta N)


/-- On a nonempty stage window, the total threshold is strictly below one.
This is the strict bound needed by the counted stopping driver. -/
theorem fullyAutomaticDeltaThreshold_lt_one
    (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) {N : Nat} (N_pos : 1 <= N)
    (gapEpsilon : Real) :
    fullyAutomaticDeltaThreshold iota eta N gapEpsilon < 1 := by
  calc
    fullyAutomaticDeltaThreshold iota eta N gapEpsilon <=
        fullyAutomaticDeltaThetaCap iota eta N :=
      fullyAutomaticDeltaThreshold_le_cap iota eta N gapEpsilon
    _ <=
        FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2.automaticOneStepSmallThetaThreshold
          (Fintype.card iota) (eta 0) := by
      exact uniformAutomaticThetaThreshold_le_stage
        (Fintype.card iota) eta N 0 N_pos
    _ <= (2 : NNReal)⁻¹ := min_le_left _ _
    _ < 1 := by norm_num

/-- A single non-strict total-threshold assumption gives the strict
`delta < 1` premise whenever the recursion has at least one stage. -/
theorem delta_lt_one_of_le_fullyAutomaticDeltaThreshold
    (N_pos : 1 <= N)
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    delta < 1 :=
  delta_le.trans_lt
    (fullyAutomaticDeltaThreshold_lt_one iota eta N_pos gapEpsilon)

theorem le_fullyAutomaticDeltaThreshold_iff
    (delta : NNReal) (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) :
    delta <= fullyAutomaticDeltaThreshold iota eta N gapEpsilon <->
      delta <= cappedSeedDeltaThreshold
          (fullyAutomaticDeltaThetaCap iota eta N) gapEpsilon /\
        delta <= uniformFirstNonLargeAdjacentCardThreshold
          iota gapEpsilon eta N := by
  exact le_min_iff

/-! ## One-shot projection to the two consumers -/

/-- The total threshold supplies exactly the pair of bounds needed to build
the capped seed. -/
theorem cappedSeedDeltaBounds_of_le_fullyAutomaticDeltaThreshold
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    delta <= fullyAutomaticDeltaThetaCap iota eta N /\
      (delta : ENNReal) ^ gapEpsilon <=
        (fullyAutomaticDeltaThetaCap iota eta N : ENNReal) := by
  exact cappedSeedDeltaBounds_of_le_threshold
    (fullyAutomaticDeltaThetaCap_pos iota eta N) gap_pos
    (delta_le.trans
      (fullyAutomaticDeltaThreshold_le_seed iota eta N gapEpsilon))

/-- The other projection is the precomputed adjacent-card bound consumed by
the uniform recovered endpoint. -/
theorem uniformAdjacentBound_of_le_fullyAutomaticDeltaThreshold
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    delta <= uniformFirstNonLargeAdjacentCardThreshold
      iota gapEpsilon eta N :=
  delta_le.trans
    (fullyAutomaticDeltaThreshold_le_uniformAdjacent
      iota eta N gapEpsilon)

/-- A bundled certificate carrying every seed and endpoint delta projection
used downstream. -/
structure FullyAutomaticDeltaThresholdBounds
    (delta : NNReal) (iota : Type*) [Fintype iota]
    (eta : Nat -> Real) (N : Nat) (gapEpsilon : Real) : Prop where
  delta_le_total :
    delta <= fullyAutomaticDeltaThreshold iota eta N gapEpsilon
  delta_le_seed :
    delta <= cappedSeedDeltaThreshold
      (fullyAutomaticDeltaThetaCap iota eta N) gapEpsilon
  delta_le_cap : delta <= fullyAutomaticDeltaThetaCap iota eta N
  delta_power_le_cap :
    (delta : ENNReal) ^ gapEpsilon <=
      (fullyAutomaticDeltaThetaCap iota eta N : ENNReal)
  delta_le_uniformAdjacent :
    delta <= uniformFirstNonLargeAdjacentCardThreshold
      iota gapEpsilon eta N
  delta_le_one : delta <= 1

/-- Construct the complete bundle from the single total-threshold
hypothesis. -/
theorem fullyAutomaticDeltaThresholdBounds_of_le
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    FullyAutomaticDeltaThresholdBounds
      delta iota eta N gapEpsilon := by
  have seed_bounds :
      delta <= fullyAutomaticDeltaThetaCap iota eta N /\
        (delta : ENNReal) ^ gapEpsilon <=
          (fullyAutomaticDeltaThetaCap iota eta N : ENNReal) :=
    cappedSeedDeltaBounds_of_le_fullyAutomaticDeltaThreshold
      gap_pos delta_le
  refine {
    delta_le_total := delta_le
    delta_le_seed := delta_le.trans
      (fullyAutomaticDeltaThreshold_le_seed iota eta N gapEpsilon)
    delta_le_cap := seed_bounds.1
    delta_power_le_cap := seed_bounds.2
    delta_le_uniformAdjacent :=
      uniformAdjacentBound_of_le_fullyAutomaticDeltaThreshold delta_le
    delta_le_one := delta_le.trans
      (fullyAutomaticDeltaThreshold_le_one iota eta N gapEpsilon) }

namespace FullyAutomaticDeltaThresholdBounds

/-- Recover the exact pair consumed by `cappedSeedScaleSequence`. -/
theorem toCappedSeedBounds
    (bounds : FullyAutomaticDeltaThresholdBounds
      delta iota eta N gapEpsilon) :
    delta <= fullyAutomaticDeltaThetaCap iota eta N /\
      (delta : ENNReal) ^ gapEpsilon <=
        (fullyAutomaticDeltaThetaCap iota eta N : ENNReal) :=
  ⟨bounds.delta_le_cap, bounds.delta_power_le_cap⟩

/-- Project further to the concrete adjacent threshold of any stage in the
counted window `1 <= stage <= N`. -/
theorem delta_le_adjacentStage
    (bounds : FullyAutomaticDeltaThresholdBounds
      delta iota eta N gapEpsilon)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N) :
    delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta (stage - 1)) := by
  exact bounds.delta_le_uniformAdjacent.trans
    (uniformFirstNonLargeAdjacentCardThreshold_le_stage
      iota gapEpsilon eta N stage stage_pos stage_le)


/-- The bundled total bound also yields the counted driver strict
`delta < 1` premise on every nonempty stage window. -/
theorem delta_lt_one
    (bounds : FullyAutomaticDeltaThresholdBounds
      delta iota eta N gapEpsilon)
    (N_pos : 1 <= N) :
    delta < 1 :=
  delta_lt_one_of_le_fullyAutomaticDeltaThreshold
    N_pos bounds.delta_le_total

end FullyAutomaticDeltaThresholdBounds

#print axioms fullyAutomaticDeltaThetaCap_pos
#print axioms fullyAutomaticDeltaThetaCap_le_one
#print axioms fullyAutomaticDeltaThreshold_pos
#print axioms fullyAutomaticDeltaThreshold_le_seed
#print axioms fullyAutomaticDeltaThreshold_le_uniformAdjacent
#print axioms fullyAutomaticDeltaThreshold_le_cap
#print axioms fullyAutomaticDeltaThreshold_le_one
#print axioms fullyAutomaticDeltaThreshold_lt_one
#print axioms delta_lt_one_of_le_fullyAutomaticDeltaThreshold
#print axioms cappedSeedDeltaBounds_of_le_fullyAutomaticDeltaThreshold
#print axioms uniformAdjacentBound_of_le_fullyAutomaticDeltaThreshold
#print axioms fullyAutomaticDeltaThresholdBounds_of_le
#print axioms FullyAutomaticDeltaThresholdBounds.delta_le_adjacentStage
#print axioms FullyAutomaticDeltaThresholdBounds.delta_lt_one

end
end FamilyStickyScaleChainFullyAutomaticDeltaThresholdV2
