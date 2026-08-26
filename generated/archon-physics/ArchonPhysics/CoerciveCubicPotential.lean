import Mathlib

/-!
# A coercive cubic-leading weak-interaction potential

The pure odd polynomial used in the motivating lattice model is not bounded
below.  This module fixes a concrete cubic-leading family with a stabilizing
quartic term and proves its uniform quadratic lower bound.  It is a finite
algebraic ingredient for a later global-flow theorem; it makes no kinetic or
thermalization claim.
-/

namespace ArchonPhysics.CoerciveCubicPotential

noncomputable section

/-- The concrete weak-interaction potential
`x²/2 + (κg/3)x³ + (βg²/4)x⁴`. -/
def potential (κ β g x : Real) : Real :=
  x ^ 2 / 2 + (κ * g / 3) * x ^ 3 + (β * g ^ 2 / 4) * x ^ 4

/-- The uniform quadratic coercivity constant obtained by completing the square. -/
def coercivityConstant (κ β : Real) : Real :=
  1 / 2 - κ ^ 2 / (9 * β)

/-- The potential factors into `x²` times a quadratic polynomial in `g*x`. -/
theorem potential_factor (κ β g x : Real) :
    potential κ β g x =
      x ^ 2 * (1 / 2 + (κ / 3) * (g * x) + (β / 4) * (g * x) ^ 2) := by
  unfold potential
  ring

/-- The parameter inequality used below forces a strictly positive quartic coefficient. -/
theorem beta_pos {κ β : Real} (hβ : 2 * κ ^ 2 / 9 < β) : 0 < β := by
  have hthreshold : 0 ≤ 2 * κ ^ 2 / 9 := by positivity
  exact lt_of_le_of_lt hthreshold hβ

/-- Under `β > 2κ²/9`, the uniform coercivity constant is strictly positive. -/
theorem coercivityConstant_pos {κ β : Real} (hβ : 2 * κ ^ 2 / 9 < β) :
    0 < coercivityConstant κ β := by
  have hβpos : 0 < β := beta_pos hβ
  have hden : 0 < 9 * β := mul_pos (by norm_num) hβpos
  have hfrac : κ ^ 2 / (9 * β) < 1 / 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith [hβ]
  unfold coercivityConstant
  linarith

/-- Completing the square gives a uniform-in-`g` quadratic lower bound. -/
theorem potential_lower_bound {κ β : Real} (hβ : 2 * κ ^ 2 / 9 < β)
    (g x : Real) :
    coercivityConstant κ β * x ^ 2 ≤ potential κ β g x := by
  have hβpos : 0 < β := beta_pos hβ
  have hβne : β ≠ 0 := ne_of_gt hβpos
  let y : Real := g * x
  have hcomplete :
      κ ^ 2 / (9 * β) + (κ / 3) * y + (β / 4) * y ^ 2 =
        (β / 4) * (y + 2 * κ / (3 * β)) ^ 2 := by
    field_simp [hβne]
    ring
  have hsquare :
      0 ≤ κ ^ 2 / (9 * β) + (κ / 3) * y + (β / 4) * y ^ 2 := by
    rw [hcomplete]
    positivity
  have hquadratic :
      coercivityConstant κ β ≤
        1 / 2 + (κ / 3) * y + (β / 4) * y ^ 2 := by
    unfold coercivityConstant
    linarith
  rw [potential_factor]
  change coercivityConstant κ β * x ^ 2 ≤
    x ^ 2 * (1 / 2 + (κ / 3) * y + (β / 4) * y ^ 2)
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hquadratic (sq_nonneg x))

/-- In particular, the stabilized cubic-leading potential is nonnegative. -/
theorem potential_nonneg {κ β : Real} (hβ : 2 * κ ^ 2 / 9 < β)
    (g x : Real) : 0 ≤ potential κ β g x := by
  calc
    0 ≤ coercivityConstant κ β * x ^ 2 :=
      mul_nonneg (le_of_lt (coercivityConstant_pos hβ)) (sq_nonneg x)
    _ ≤ potential κ β g x := potential_lower_bound hβ g x

/-- Formula-level lock for the potential and its coercivity constant. -/
theorem potential_spec (κ β g x : Real) :
    potential κ β g x =
        x ^ 2 / 2 + (κ * g / 3) * x ^ 3 + (β * g ^ 2 / 4) * x ^ 4 ∧
      coercivityConstant κ β = 1 / 2 - κ ^ 2 / (9 * β) := by
  exact ⟨rfl, rfl⟩

end

end ArchonPhysics.CoerciveCubicPotential
