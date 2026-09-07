import Family8Grounding.Family8IdentityCoreSourceKatzTaoBootstrapV1
import Mathlib.Tactic

/-!
# The identity-radius Katz--Tao loss is not a relative-scale loss

At the fixed coarse radius `1/2`, the identity-radius volume ratio diverges
as the fine radius tends to zero.  In particular, fixing the interval ratio
`b / tau = 1` cannot bound it.  This is the scalar obstruction to absorbing
the identity-cover Katz--Tao loss using only long-interval `b / tau` data.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8IdentityRadiusRatioUnboundedV1

open Family8IdentityCoreSourceKatzTaoBootstrapV1

noncomputable section

/-- A positive fine radius below `1/2` chosen to make the identity loss
larger than a prescribed finite target. -/
def identityRatioCounterRadius (M : NNReal) : NNReal :=
  (2 * (M + 1))⁻¹

theorem identityRatioCounterRadius_pos (M : NNReal) :
    0 < identityRatioCounterRadius M := by
  unfold identityRatioCounterRadius
  positivity

theorem identityRatioCounterRadius_le_half (M : NNReal) :
    identityRatioCounterRadius M <= (2 : NNReal)⁻¹ := by
  unfold identityRatioCounterRadius
  apply inv_anti₀ (by norm_num : (0 : NNReal) < 2)
  nlinarith

/-- The explicit ratio at the counter-radius is a growing quadratic. -/
theorem identityRadiusRatio_counterRadius_eq (M : NNReal) :
    identityRadiusKatzTaoVolumeRatioNNReal
        (identityRatioCounterRadius M) (2 : NNReal)⁻¹ =
      16 * (M + 1) ^ 2 := by
  have hM : M + 1 ≠ 0 := by positivity
  unfold identityRadiusKatzTaoVolumeRatioNNReal
    identityRatioCounterRadius
  field_simp
  ring

/-- Every finite target is exceeded at some legal fine radius while the
coarse radius remains exactly `1/2`. -/
theorem exists_identityRadiusRatio_ge (M : NNReal) :
    ∃ delta : NNReal,
      0 < delta ∧ delta <= (2 : NNReal)⁻¹ ∧
        M <= identityRadiusKatzTaoVolumeRatioNNReal
          delta (2 : NNReal)⁻¹ := by
  refine ⟨identityRatioCounterRadius M,
    identityRatioCounterRadius_pos M,
    identityRatioCounterRadius_le_half M, ?_⟩
  rw [identityRadiusRatio_counterRadius_eq]
  nlinarith [sq_nonneg (M + 1)]

/-- Consequently no finite constant can uniformly bound the identity loss
at a fixed coarse radius, even before any long-interval algebra is used. -/
theorem no_uniform_identityRadiusRatio_bound :
    ¬ ∃ B : NNReal, ∀ delta : NNReal,
      0 < delta -> delta <= (2 : NNReal)⁻¹ ->
        identityRadiusKatzTaoVolumeRatioNNReal
          delta (2 : NNReal)⁻¹ <= B := by
  rintro ⟨B, hB⟩
  obtain ⟨delta, hdeltaPos, hdeltaHalf, hlarge⟩ :=
    exists_identityRadiusRatio_ge (B + 1)
  have hupper := hB delta hdeltaPos hdeltaHalf
  nlinarith

#print axioms identityRatioCounterRadius_pos
#print axioms identityRatioCounterRadius_le_half
#print axioms identityRadiusRatio_counterRadius_eq
#print axioms exists_identityRadiusRatio_ge
#print axioms no_uniform_identityRadiusRatio_bound

end

end Family8IdentityRadiusRatioUnboundedV1
