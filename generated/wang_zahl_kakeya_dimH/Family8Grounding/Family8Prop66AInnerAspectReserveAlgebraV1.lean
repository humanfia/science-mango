import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# Exact algebra of the quadratic-aspect reserve in Equation (46)

Once the natural fibre cap contributes `(b/a)^2`, all aspect powers in the
inner Proposition 6.6(A) expression combine to the single favourable factor
`b/a`.  The remaining scale exponent is exactly `2 - 3 beta`.
-/

open scoped ENNReal NNReal

namespace Family8Prop66AInnerAspectReserveAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

theorem proposition66AInner_aspectReserve_eq
    {d a b : NNReal} {epsilon beta : Real}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hbetaTwo : beta <= 2) :
    (d : ENNReal) ^ (-epsilon / 2) *
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta) *
      ((d : ENNReal) / (a : ENNReal)) ^ (-2 * beta) *
        (((((d : ENNReal) / (a : ENNReal)) ^ (2 : Nat)) *
          (((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat))) ^
            (1 - beta / 2)) =
      (d : ENNReal) ^ (-epsilon / 2) *
        ((b : ENNReal) / (a : ENNReal)) *
          (((d : ENNReal) / (a : ENNReal)) ^ (2 - 3 * beta)) := by
  let D : ENNReal := d
  let A : ENNReal := a
  let B : ENNReal := b
  let x : ENNReal := A / B
  let y : ENNReal := D / A
  let p : Real := 1 - beta / 2
  let q : Real := 2 - 3 * beta
  have hp : 0 <= p := by dsimp only [p]; linarith
  have hD0 : D ≠ 0 := by
    dsimp only [D]
    exact ENNReal.coe_ne_zero.mpr hd.ne'
  have hA0 : A ≠ 0 := by
    dsimp only [A]
    exact ENNReal.coe_ne_zero.mpr ha.ne'
  have hB0 : B ≠ 0 := by
    dsimp only [B]
    exact ENNReal.coe_ne_zero.mpr hb.ne'
  have hDTop : D ≠ ∞ := by simp [D]
  have hATop : A ≠ ∞ := by simp [A]
  have hBTop : B ≠ ∞ := by simp [B]
  have hx0 : x ≠ 0 := by
    dsimp only [x]
    exact ENNReal.div_ne_zero.mpr ⟨hA0, hBTop⟩
  have hxTop : x ≠ ∞ := by
    dsimp only [x]
    exact ENNReal.div_ne_top hATop hB0
  have hy0 : y ≠ 0 := by
    dsimp only [y]
    exact ENNReal.div_ne_zero.mpr ⟨hD0, hATop⟩
  have hyTop : y ≠ ∞ := by
    dsimp only [y]
    exact ENNReal.div_ne_top hDTop hA0
  have hrecip : B / A = x⁻¹ := by
    dsimp only [x]
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hATop), inv_inv]
    ac_rfl
  have hsquareReserve :
      ((y ^ (2 : Nat)) * ((B / A) ^ (2 : Nat))) ^ p =
        y ^ (2 * p) * x ^ (-(2 * p)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp, hrecip]
    congr 1
    · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      norm_num
  have hxcombine : x ^ (1 - beta) * x ^ (-(2 * p)) = B / A := by
    calc
      x ^ (1 - beta) * x ^ (-(2 * p)) =
          x ^ ((1 - beta) + (-(2 * p))) := by
        rw [ENNReal.rpow_add (1 - beta) (-(2 * p)) hx0 hxTop]
      _ = x ^ (-1 : Real) := by
        congr 1
        dsimp only [p]
        ring
      _ = x⁻¹ := by rw [ENNReal.rpow_neg_one]
      _ = B / A := hrecip.symm
  have hycombine : y ^ (-2 * beta) * y ^ (2 * p) = y ^ q := by
    calc
      y ^ (-2 * beta) * y ^ (2 * p) =
          y ^ ((-2 * beta) + 2 * p) := by
        rw [ENNReal.rpow_add (-2 * beta) (2 * p) hy0 hyTop]
      _ = y ^ q := by
        congr 1
        dsimp only [p, q]
        ring
  change
    D ^ (-epsilon / 2) * x ^ (1 - beta) * y ^ (-2 * beta) *
        (((y ^ (2 : Nat)) * ((B / A) ^ (2 : Nat))) ^ p) =
      D ^ (-epsilon / 2) * (B / A) * y ^ q
  rw [hsquareReserve]
  calc
    D ^ (-epsilon / 2) * x ^ (1 - beta) * y ^ (-2 * beta) *
        (y ^ (2 * p) * x ^ (-(2 * p))) =
      D ^ (-epsilon / 2) *
        (x ^ (1 - beta) * x ^ (-(2 * p))) *
          (y ^ (-2 * beta) * y ^ (2 * p)) := by ac_rfl
    _ = D ^ (-epsilon / 2) * (B / A) * y ^ q := by
      rw [hxcombine, hycombine]

#print axioms proposition66AInner_aspectReserve_eq

end
end Family8Prop66AInnerAspectReserveAlgebraV1
