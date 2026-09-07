import Family8Grounding.Family8ZeroColorPolynomialJohnKatzTaoV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8KatzTaoSamplingMultiplicityV1

open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Automatic sampling multiplicity for generalized Katz--Tao

For a positive finite source Katz--Tao constant `C`, sampling with
`k = ceil(C.toReal)` makes the expected normalized test load at most one.
When `C ≥ 1`, this integer costs at most `2C`, which is the paper's
`C^(1-beta)` factor after the sampled multiplicity estimate is returned to
the source datum.
-/

def katzTaoSamplingMultiplicity (C : ENNReal) : Nat :=
  Nat.ceil C.toReal

theorem katzTaoSamplingMultiplicity_pos
    {C : ENNReal} (hCpos : 0 < C) (hCfinite : C ≠ ∞) :
    0 < katzTaoSamplingMultiplicity C := by
  unfold katzTaoSamplingMultiplicity
  rw [Nat.ceil_pos]
  exact ENNReal.toReal_pos hCpos.ne' hCfinite

theorem toReal_div_katzTaoSamplingMultiplicity_le_one
    {C : ENNReal} (hCpos : 0 < C) (hCfinite : C ≠ ∞) :
    C.toReal / (katzTaoSamplingMultiplicity C : Real) ≤ 1 := by
  have hk : 0 < katzTaoSamplingMultiplicity C :=
    katzTaoSamplingMultiplicity_pos hCpos hCfinite
  apply (div_le_one (by exact_mod_cast hk)).2
  exact Nat.le_ceil C.toReal

theorem katzTaoSamplingMultiplicity_cast_lt_toReal_add_one
    (C : ENNReal) :
    (katzTaoSamplingMultiplicity C : Real) < C.toReal + 1 := by
  unfold katzTaoSamplingMultiplicity
  exact Nat.ceil_lt_add_one (ENNReal.toReal_nonneg)

/-- In the regime `1 ≤ C`, the selected integer is at most twice `C` in
`Real`. -/
theorem katzTaoSamplingMultiplicity_cast_le_two_mul_toReal
    {C : ENNReal} (hC : 1 ≤ C) (hCfinite : C ≠ ∞) :
    (katzTaoSamplingMultiplicity C : Real) ≤ 2 * C.toReal := by
  have hCReal : 1 ≤ C.toReal := by
    simpa using (ENNReal.toReal_le_toReal (by simp) hCfinite).2 hC
  exact (katzTaoSamplingMultiplicity_cast_lt_toReal_add_one C).le.trans
    (by linarith)

/-- The same `2C` bound in the native `ENNReal` arithmetic of multiplicity
estimates. -/
theorem katzTaoSamplingMultiplicity_coe_le_two_mul
    {C : ENNReal} (hC : 1 ≤ C) (hCfinite : C ≠ ∞) :
    (katzTaoSamplingMultiplicity C : ENNReal) ≤ 2 * C := by
  have hrightTop : (2 : ENNReal) * C ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hCfinite
  apply (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hrightTop).mp
  simpa [ENNReal.toReal_mul, hCfinite] using
    katzTaoSamplingMultiplicity_cast_le_two_mul_toReal hC hCfinite

#print axioms katzTaoSamplingMultiplicity_pos
#print axioms toReal_div_katzTaoSamplingMultiplicity_le_one
#print axioms katzTaoSamplingMultiplicity_cast_lt_toReal_add_one
#print axioms katzTaoSamplingMultiplicity_cast_le_two_mul_toReal
#print axioms katzTaoSamplingMultiplicity_coe_le_two_mul

end
end Family8KatzTaoSamplingMultiplicityV1
