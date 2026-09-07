import Family8Grounding.Family8CanonicalFullGreedyExactAssemblyChoiceV3
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Power envelope for the canonical full greedy assembly loss

The literal exact-assembly loss is a cubic polynomial in the number of active
parents (the greedy block count is at most that same number).  This module
turns an actual parent-card power bound into a power bound for that exact
loss, absorbing only the fixed constant sixteen at an explicit positive
small-scale threshold.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open scoped ENNReal NNReal

namespace Family8CanonicalFullGreedyAssemblyLossPowerV1

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CanonicalFullGreedyPartitionChoiceV4
open Family8CanonicalFullGreedyExactAssemblyChoiceV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def canonicalFullGreedyAssemblyLossPowerThreshold
    (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 16 absorbExponent

theorem canonicalFullGreedyAssemblyLossPowerThreshold_pos
    (absorbExponent : Real) :
    0 < canonicalFullGreedyAssemblyLossPowerThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- The literal loss is at most twice the cube of one plus the number of
active parents. -/
theorem canonicalFullGreedyAssemblyLoss_le_two_mul_parentSucc_cube
    (S : StickyScaleCover fine rho) :
    canonicalFullGreedyAssemblyLoss S ≤
      2 * (Fintype.card (ActiveParentIndex S) + 1) ^ 3 := by
  let N := Fintype.card (ActiveParentIndex S)
  let L := (canonicalFullGreedyPartition S).length
  have hL : L ≤ N := canonicalFullGreedyPartition_length_le S
  have hoption : Fintype.card (Option (Fin L)) + 1 ≤ 2 * (N + 1) := by
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  unfold canonicalFullGreedyAssemblyLoss
  rw [blocks_length]
  dsimp only [N, L] at hoption ⊢
  calc
    ((Fintype.card (ActiveParentIndex S) + 1) *
        (Fintype.card (ActiveParentIndex S) + 1)) *
          (Fintype.card
            (Option (Fin (canonicalFullGreedyPartition S).length)) + 1) ≤
      ((Fintype.card (ActiveParentIndex S) + 1) *
        (Fintype.card (ActiveParentIndex S) + 1)) *
          (2 * (Fintype.card (ActiveParentIndex S) + 1)) :=
      Nat.mul_le_mul_left _ hoption
    _ = 2 * (Fintype.card (ActiveParentIndex S) + 1) ^ 3 := by ring

/-- Any actual delta-power bound for the active-parent card gives the
corresponding cubic bound for the exact canonical assembly loss. -/
theorem canonicalFullGreedyAssemblyLoss_le_delta_negativePower
    (S : StickyScaleCover fine rho)
    {parentExponent absorbExponent : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hparentExponent : 0 ≤ parentExponent)
    (hparentCard :
      (Fintype.card (ActiveParentIndex S) : ENNReal) ≤
        (delta : ENNReal) ^ (-parentExponent))
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      canonicalFullGreedyAssemblyLossPowerThreshold absorbExponent) :
    (canonicalFullGreedyAssemblyLoss S : ENNReal) ≤
      (delta : ENNReal) ^ (-(3 * parentExponent + absorbExponent)) := by
  let N := Fintype.card (ActiveParentIndex S)
  let x : ENNReal := (delta : ENNReal) ^ (-parentExponent)
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hxOne : 1 ≤ x := by
    dsimp only [x]
    rcases hparentExponent.eq_or_lt with hp0 | hp
    · subst parentExponent
      simpa only [neg_zero, ENNReal.rpow_zero] using (le_refl (1 : ENNReal))
    · exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
        (ENNReal.coe_pos.mpr hdelta)
        (ENNReal.coe_le_coe.mpr hdeltaOne)
        (neg_lt_zero.mpr hp)
  have hN : (N : ENNReal) ≤ x := by
    simpa only [N, x] using hparentCard
  have hNsucc : (N : ENNReal) + 1 ≤ 2 * x := by
    calc
      (N : ENNReal) + 1 ≤ x + x := add_le_add hN hxOne
      _ = 2 * x := by ring
  have hpolyNat := canonicalFullGreedyAssemblyLoss_le_two_mul_parentSucc_cube S
  have hpoly : (canonicalFullGreedyAssemblyLoss S : ENNReal) ≤
      (2 : ENNReal) * ((N : ENNReal) + 1) ^ 3 := by
    exact_mod_cast hpolyNat
  have hconst : (16 : ENNReal) ≤
      (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      habsorbExponent hdelta hsmall
  calc
    (canonicalFullGreedyAssemblyLoss S : ENNReal) ≤
        (2 : ENNReal) * ((N : ENNReal) + 1) ^ 3 := hpoly
    _ ≤ (2 : ENNReal) * (2 * x) ^ 3 :=
      mul_le_mul' le_rfl (pow_le_pow_left' hNsucc 3)
    _ = (16 : ENNReal) * x ^ 3 := by ring
    _ ≤ (delta : ENNReal) ^ (-absorbExponent) * x ^ 3 :=
      mul_le_mul' hconst le_rfl
    _ = (delta : ENNReal) ^
        (-(3 * parentExponent + absorbExponent)) := by
      dsimp only [x]
      rw [← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

#print axioms canonicalFullGreedyAssemblyLossPowerThreshold_pos
#print axioms canonicalFullGreedyAssemblyLoss_le_two_mul_parentSucc_cube
#print axioms canonicalFullGreedyAssemblyLoss_le_delta_negativePower

end
end Family8CanonicalFullGreedyAssemblyLossPowerV1
