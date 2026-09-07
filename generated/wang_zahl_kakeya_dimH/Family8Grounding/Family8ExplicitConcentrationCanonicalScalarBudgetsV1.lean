import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ExplicitConcentrationCanonicalScalarBudgetsV1

open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Fixed `128` budgets for the canonical B2-to-unit datum

These two scalar facts discharge the only normalization constants exposed by
the canonical full-coarse specialization: the transported Katz--Tao constant
is `128 * C`, and the transported full-shading density is at least `1 / 128`.
-/

def canonicalOuterScalarThreshold
    (C : ENNReal) (sourceEta sourceDensityEta : Real) : NNReal :=
  min
    (finiteConstantSmallDeltaThreshold (128 * C) sourceEta)
    (finiteConstantSmallDeltaThreshold 128 sourceDensityEta)

theorem canonicalOuterScalarThreshold_pos
    (C : ENNReal) (sourceEta sourceDensityEta : Real) :
    0 < canonicalOuterScalarThreshold C sourceEta sourceDensityEta := by
  rw [canonicalOuterScalarThreshold, lt_min_iff]
  exact ⟨finiteConstantSmallDeltaThreshold_pos _ _,
    finiteConstantSmallDeltaThreshold_pos _ _⟩

theorem normalizedKatzTaoConstant_le_negativePower
    {rho : NNReal} {C : ENNReal} {sourceEta sourceDensityEta : Real}
    (hrho : 0 < rho) (hCfinite : C ≠ ∞) (hsourceEta : 0 < sourceEta)
    (hsmall : rho ≤
      canonicalOuterScalarThreshold C sourceEta sourceDensityEta) :
    128 * C ≤ (rho : ENNReal) ^ (-sourceEta) := by
  apply finiteConstant_le_delta_negativePower
  · exact ENNReal.mul_ne_top (by norm_num) hCfinite
  · exact hsourceEta
  · exact hrho
  · exact hsmall.trans (min_le_left _ _)

theorem densityPower_le_one_div_128
    {rho : NNReal} {C : ENNReal} {sourceEta sourceDensityEta : Real}
    (hrho : 0 < rho) (hsourceDensityEta : 0 < sourceDensityEta)
    (hsmall : rho ≤
      canonicalOuterScalarThreshold C sourceEta sourceDensityEta) :
    (rho : ENNReal) ^ sourceDensityEta ≤ 1 / 128 := by
  have hconstant : (128 : ENNReal) ≤
      (rho : ENNReal) ^ (-sourceDensityEta) := by
    apply finiteConstant_le_delta_negativePower
    · norm_num
    · exact hsourceDensityEta
    · exact hrho
    · exact hsmall.trans (min_le_right _ _)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by norm_num : (128 : ENNReal) ≠ 0))
    (Or.inl (by norm_num : (128 : ENNReal) ≠ ∞))).2
  calc
    (rho : ENNReal) ^ sourceDensityEta * 128 ≤
        (rho : ENNReal) ^ sourceDensityEta *
          (rho : ENNReal) ^ (-sourceDensityEta) :=
      mul_le_mul' le_rfl hconstant
    _ = (rho : ENNReal) ^ (sourceDensityEta + (-sourceDensityEta)) := by
      rw [ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hrho.ne')
        ENNReal.coe_ne_top]
    _ = 1 := by simp

#print axioms canonicalOuterScalarThreshold_pos
#print axioms normalizedKatzTaoConstant_le_negativePower
#print axioms densityPower_le_one_div_128

end
end Family8ExplicitConcentrationCanonicalScalarBudgetsV1
