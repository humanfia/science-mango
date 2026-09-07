import Family8Grounding.Family8SphereDirectionPackingV1

open Set
open scoped ENNReal NNReal

namespace Family8SphereDirectionPackingENNRealV1

open LeanEval.Analysis.WangZahlKakeya
open Family8SphereDirectionPackingV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# ENNReal consumer for the sphere-direction packing bound

The geometric packing theorem naturally produces the integer cap
`ceil (32 delta^{-2})`.  Downstream Frostman estimates use `ENNReal` and real
exponents.  This file proves, rather than assumes, the exact conversion

`ceil (32 delta^{-2}) ≤ 33 * delta ^ (-2)`

for `0 < delta ≤ 1`.  The extra one is absorbed because `delta^{-2} ≥ 1`.
-/

/-- The canonical natural direction-packing cap. -/
def directionPackingNatCap (delta : NNReal) : Nat :=
  Nat.ceil (32 * ((delta : Real)⁻¹) ^ 2)

/-- The ceiling loses at most one, and that one is absorbed by
`delta^{-2} ≥ 1`. -/
theorem directionPackingNatCap_real_le_invSq
    (delta : NNReal) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (directionPackingNatCap delta : Real) ≤
      33 * ((delta : Real)⁻¹) ^ 2 := by
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdelta
  have hdeltaRealOne : (delta : Real) ≤ 1 := by exact_mod_cast hdeltaOne
  have hinv : 1 ≤ (delta : Real)⁻¹ :=
    (one_le_inv₀ hdeltaReal).2 hdeltaRealOne
  have hinvSq : 1 ≤ ((delta : Real)⁻¹) ^ 2 := by
    nlinarith [sq_nonneg ((delta : Real)⁻¹ - 1)]
  have hxnonneg : 0 ≤ 32 * ((delta : Real)⁻¹) ^ 2 := by positivity
  calc
    (directionPackingNatCap delta : Real) ≤
        32 * ((delta : Real)⁻¹) ^ 2 + 1 := by
      simpa only [directionPackingNatCap] using
        (Nat.ceil_lt_add_one hxnonneg).le
    _ ≤ 33 * ((delta : Real)⁻¹) ^ 2 := by nlinarith

/-- Real `rpow` form of the cap bound. -/
theorem directionPackingNatCap_real_le_rpow
    (delta : NNReal) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (directionPackingNatCap delta : Real) ≤
      33 * (delta : Real) ^ (-2 : Real) := by
  have h := directionPackingNatCap_real_le_invSq delta hdelta hdeltaOne
  have hrpow :
      (delta : Real) ^ (-2 : Real) = ((delta : Real)⁻¹) ^ 2 := by
    rw [show (-2 : Real) = ((-2 : Int) : Real) by norm_num,
      Real.rpow_intCast]
    norm_num [zpow_neg]
  rwa [hrpow]

/-- The canonical natural cap has the required explicit `ENNReal` size. -/
theorem directionPackingNatCap_coe_le_rpow
    (delta : NNReal) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (directionPackingNatCap delta : ENNReal) ≤
      33 * (delta : ENNReal) ^ (-2 : Real) := by
  have hreal :=
    directionPackingNatCap_real_le_rpow delta hdelta hdeltaOne
  have hnn :
      (directionPackingNatCap delta : NNReal) ≤
        33 * delta ^ (-2 : Real) := by
    rw [← NNReal.coe_le_coe]
    simpa only [NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_ofNat,
      NNReal.coe_rpow] using hreal
  rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-2 : Real)]
  exact_mod_cast hnn

/-- A pairwise separated finite direction family admits one natural cap
which controls both its cardinality and its `ENNReal` scale size. -/
theorem exists_directionPackingNatCap
    {index : Type} [DecidableEq index]
    (indices : Finset index) (direction : index → Space) (delta : NNReal)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      (delta : Real) ≤ dist (direction i) (direction j)) :
    ∃ M : Nat,
      indices.card ≤ M ∧
        (M : ENNReal) ≤ 33 * (delta : ENNReal) ^ (-2 : Real) := by
  refine ⟨directionPackingNatCap delta, ?_, ?_⟩
  · exact directionFinset_card_le_natCeil_thirtyTwo_mul_inv_sq
      indices direction delta hdelta hdeltaOne hunit hsep
  · exact directionPackingNatCap_coe_le_rpow delta hdelta hdeltaOne

#print axioms directionPackingNatCap_real_le_invSq
#print axioms directionPackingNatCap_real_le_rpow
#print axioms directionPackingNatCap_coe_le_rpow
#print axioms exists_directionPackingNatCap

end

end Family8SphereDirectionPackingENNRealV1
