import Family8Grounding.Family8Def212CUniformDyadicBridgeV2
import FamilyStickyGrounding.FamilyStickyScaleCoverAdjacentStepBridgeV2
import Mathlib.Tactic

/-!
# Actual Sticky-fibre uniformity gives the Proposition 6.6(A) count loss

For a chosen active parent, `C`-uniformity bounds its fibre cardinality by
`C` times every other active fibre cardinality.  Summing this literal
inequality over the exact index partition gives

`#activeParents * #chosenFibre <= C * #activeFine`.

This is precisely the multiplicative count comparison consumed by the
uniform-count form of Proposition 6.6(A).
-/

open scoped ENNReal NNReal BigOperators

namespace Family8StickyUniformCountLossV2

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleCoverAdjacentStepBridgeV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Exact cardinality partition of a Sticky cover into its active fibres. -/
theorem activeFine_card_eq_sum_fiber_card
    (S : StickyScaleCover fine rho) :
    S.activeFine.card =
      ∑ k ∈ S.activeCoarse, (S.fiber k).card := by
  change S.activeFine.card =
    ∑ k ∈ S.activeCoarse,
      (S.activeFine.filter fun i => S.parent i = k).card
  exact Finset.card_eq_sum_card_fiberwise S.parent_mem

/-- One chosen actual fibre times the number of active parents is controlled
by the total active cardinality with the literal uniformity constant. -/
theorem activeCoarse_card_mul_fiber_card_le_uniformity_mul_activeFine_card
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (huniform : IsCUniform S C)
    (k0 : Fin S.coarseCard) (hk0 : k0 ∈ S.activeCoarse) :
    ((S.activeCoarse.card * (S.fiber k0).card : Nat) : ENNReal) ≤
      C * (S.activeFine.card : ENNReal) := by
  have hpartitionNat := activeFine_card_eq_sum_fiber_card S
  have hpartitionENN : (S.activeFine.card : ENNReal) =
      ∑ k ∈ S.activeCoarse, ((S.fiber k).card : ENNReal) := by
    exact_mod_cast hpartitionNat
  calc
    ((S.activeCoarse.card * (S.fiber k0).card : Nat) : ENNReal) =
        ∑ _k ∈ S.activeCoarse, ((S.fiber k0).card : ENNReal) := by
      rw [Nat.cast_mul]
      simp
    _ ≤ ∑ k ∈ S.activeCoarse,
        C * ((S.fiber k).card : ENNReal) := by
      exact Finset.sum_le_sum fun k hk => huniform k0 hk0 k hk
    _ = C * (S.activeFine.card : ENNReal) := by
      rw [← Finset.mul_sum, ← hpartitionENN]

/-- The same comparison against the full ambient index type, ready for an
`ActualTubeDatum` whose inactive indices have not yet been reindexed away. -/
theorem activeCoarse_card_mul_fiber_card_le_uniformity_mul_total_card
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (huniform : IsCUniform S C)
    (k0 : Fin S.coarseCard) (hk0 : k0 ∈ S.activeCoarse) :
    ((S.activeCoarse.card * (S.fiber k0).card : Nat) : ENNReal) ≤
      C * (Fintype.card iota : ENNReal) := by
  calc
    ((S.activeCoarse.card * (S.fiber k0).card : Nat) : ENNReal) ≤
        C * (S.activeFine.card : ENNReal) :=
      activeCoarse_card_mul_fiber_card_le_uniformity_mul_activeFine_card
        S huniform k0 hk0
    _ ≤ C * (Fintype.card iota : ENNReal) := by
      exact mul_le_mul' le_rfl (by
        exact_mod_cast Finset.card_le_univ S.activeFine)

#print axioms activeFine_card_eq_sum_fiber_card
#print axioms
  activeCoarse_card_mul_fiber_card_le_uniformity_mul_activeFine_card
#print axioms
  activeCoarse_card_mul_fiber_card_le_uniformity_mul_total_card

end
end Family8StickyUniformCountLossV2
