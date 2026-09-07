import Mathlib.Tactic

/-! Clean quotient refold; V1 and V2 are frozen drafts. -/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8IdentityMassPopularDensityQuotientV3

/-- Refold the combined retained-density power into the exact quotient shape
consumed by the fresh low-CF endpoint. -/
theorem rpow_le_density_div_negativePower_of_combined
    {scale density : ENNReal} {eta p a : Real}
    (hscale0 : scale ≠ 0) (hscaleTop : scale ≠ ∞)
    (hcombined : scale ^ (eta - (p + a)) ≤ density) :
    scale ^ eta ≤ density / scale ^ (-(p + a)) := by
  have hscalePos : 0 < scale := bot_lt_iff_ne_bot.mpr hscale0
  have hden0 : scale ^ (-(p + a)) ≠ 0 :=
    (ENNReal.rpow_pos hscalePos hscaleTop).ne'
  have hdenTop : scale ^ (-(p + a)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hscale0 hscaleTop
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)).2
  calc
    scale ^ eta * scale ^ (-(p + a)) =
        scale ^ (eta - (p + a)) := by
      rw [← ENNReal.rpow_add _ _ hscale0 hscaleTop]
      congr 1
    _ ≤ density := hcombined

#print axioms rpow_le_density_div_negativePower_of_combined

end Family8IdentityMassPopularDensityQuotientV3
