import Family8Grounding.Family8KatzTaoSamplingMultiplicityV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8KatzTaoSamplingDensityBudgetV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoSamplingMultiplicityV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Automatic density budget for generalized Katz--Tao sampling

If the source concentration is at most `delta^(-sourceEta)`, then the ceiling
sampling multiplicity is at most twice that power.  The selected datum pays a
further factor two in the retention step.  Whenever
`targetEta > 2 * sourceEta`, one explicit small-scale threshold absorbs the
resulting constant four and proves the exact density premise required by the
sampled `KatzTaoAtParameters` application.
-/

def katzTaoSamplingDensityThreshold
    (targetEta sourceEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 4 (targetEta - 2 * sourceEta)

theorem katzTaoSamplingDensityThreshold_pos
    (targetEta sourceEta : Real) :
    0 < katzTaoSamplingDensityThreshold targetEta sourceEta :=
  finiteConstantSmallDeltaThreshold_pos 4 (targetEta - 2 * sourceEta)

/-- The pure power calculation behind the density budget. -/
theorem sampling_density_power_budget
    {delta : NNReal} {targetEta sourceEta : Real}
    (hdelta : 0 < delta)
    (hgap : 0 < targetEta - 2 * sourceEta)
    (hdeltaThreshold :
      delta ≤ katzTaoSamplingDensityThreshold targetEta sourceEta) :
    (delta : ENNReal) ^ targetEta *
        (4 * (delta : ENNReal) ^ (-sourceEta)) ≤
      (delta : ENNReal) ^ sourceEta := by
  have habsorb :
      (4 : ENNReal) ≤
        (delta : ENNReal) ^ (-(targetEta - 2 * sourceEta)) := by
    exact finiteConstant_le_delta_negativePower
      (K := (4 : ENNReal)) (by norm_num) hgap hdelta
      (by simpa [katzTaoSamplingDensityThreshold] using hdeltaThreshold)
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := by simp
  calc
    (delta : ENNReal) ^ targetEta *
        (4 * (delta : ENNReal) ^ (-sourceEta)) =
      4 * ((delta : ENNReal) ^ targetEta *
        (delta : ENNReal) ^ (-sourceEta)) := by ac_rfl
    _ = 4 * (delta : ENNReal) ^ (targetEta - sourceEta) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
    _ ≤ (delta : ENNReal) ^ (-(targetEta - 2 * sourceEta)) *
        (delta : ENNReal) ^ (targetEta - sourceEta) := by
      gcongr
    _ = (delta : ENNReal) ^ sourceEta := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

/-- Fully automatic `2k` density budget for the ceiling choice of `k`. -/
theorem samplingMultiplicity_densityBudget
    {delta : NNReal} {targetEta sourceEta : Real}
    {C density : ENNReal}
    (hdelta : 0 < delta)
    (hgap : 0 < targetEta - 2 * sourceEta)
    (hdeltaThreshold :
      delta ≤ katzTaoSamplingDensityThreshold targetEta sourceEta)
    (hCfinite : C ≠ ∞) (hCone : 1 ≤ C)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta))
    (hdensity : (delta : ENNReal) ^ sourceEta ≤ density) :
    (delta : ENNReal) ^ targetEta *
        (2 * (katzTaoSamplingMultiplicity C : ENNReal)) ≤ density := by
  have hk : (katzTaoSamplingMultiplicity C : ENNReal) ≤ 2 * C :=
    katzTaoSamplingMultiplicity_coe_le_two_mul hCone hCfinite
  calc
    (delta : ENNReal) ^ targetEta *
        (2 * (katzTaoSamplingMultiplicity C : ENNReal)) ≤
      (delta : ENNReal) ^ targetEta * (4 * C) := by
        apply mul_right_mono
        calc
          2 * (katzTaoSamplingMultiplicity C : ENNReal) ≤ 2 * (2 * C) :=
            mul_right_mono hk
          _ = 4 * C := by ring
    _ ≤ (delta : ENNReal) ^ targetEta *
        (4 * (delta : ENNReal) ^ (-sourceEta)) := by
      exact mul_right_mono (mul_right_mono hC)
    _ ≤ (delta : ENNReal) ^ sourceEta :=
      sampling_density_power_budget hdelta hgap hdeltaThreshold
    _ ≤ density := hdensity

#print axioms katzTaoSamplingDensityThreshold_pos
#print axioms sampling_density_power_budget
#print axioms samplingMultiplicity_densityBudget

end
end Family8KatzTaoSamplingDensityBudgetV1
