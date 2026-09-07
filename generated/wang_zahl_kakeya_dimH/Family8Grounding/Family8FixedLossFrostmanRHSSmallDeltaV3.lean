import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV4
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open scoped ENNReal NNReal

namespace Family8FixedLossFrostmanRHSSmallDeltaV3

open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanRHSScaleVolumeAlgebraV4
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- Explicit terminal scale at which a finite loss is absorbed by the
positive epsilon gap. -/
def fixedLossFrostmanRHSThreshold
    (loss : ENNReal) (innerEpsilon outerEpsilon : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold loss (outerEpsilon - innerEpsilon)

theorem fixedLossFrostmanRHSThreshold_pos
    (loss : ENNReal) (innerEpsilon outerEpsilon : Real) :
    0 < fixedLossFrostmanRHSThreshold loss innerEpsilon outerEpsilon :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem fixedLossFrostmanRHSThreshold_le_one
    (loss : ENNReal) {innerEpsilon outerEpsilon : Real}
    (hgap : innerEpsilon < outerEpsilon) :
    fixedLossFrostmanRHSThreshold loss innerEpsilon outerEpsilon ≤ 1 := by
  exact finiteConstantSmallDeltaThreshold_le_one loss (sub_pos.mpr hgap)

/-- A finite scalar multiplying a Frostman RHS is absorbed exactly by the
available epsilon gap. -/
theorem fixedLoss_mul_frostmanMultiplicityRHS_le
    {delta : NNReal} {actualVolume loss : ENNReal}
    {innerEpsilon outerEpsilon gamma : Real}
    (hdelta : 0 < delta) (hlossTop : loss ≠ ∞)
    (hgap : innerEpsilon < outerEpsilon)
    (hsmall : delta ≤
      fixedLossFrostmanRHSThreshold loss innerEpsilon outerEpsilon) :
    loss * frostmanMultiplicityRHS delta actualVolume innerEpsilon gamma ≤
      frostmanMultiplicityRHS delta actualVolume outerEpsilon gamma := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hloss : loss ≤
      (delta : ENNReal) ^ (-(outerEpsilon - innerEpsilon)) := by
    exact finiteConstant_le_delta_negativePower hlossTop
      (sub_pos.mpr hgap) hdelta hsmall
  have hpow :
      (delta : ENNReal) ^ (-(outerEpsilon - innerEpsilon)) *
          (delta : ENNReal) ^ (-innerEpsilon) =
        (delta : ENNReal) ^ (-outerEpsilon) := by
    rw [← ENNReal.rpow_add _ _ hd0 hdTop]
    congr 1
    ring
  unfold frostmanMultiplicityRHS
  calc
    loss *
          ((delta : ENNReal) ^ (-innerEpsilon) *
            (delta : ENNReal) ^ (-2 * gamma) *
              actualVolume ^ (1 - gamma / 2)) ≤
        (delta : ENNReal) ^ (-(outerEpsilon - innerEpsilon)) *
          ((delta : ENNReal) ^ (-innerEpsilon) *
            (delta : ENNReal) ^ (-2 * gamma) *
              actualVolume ^ (1 - gamma / 2)) := by
      gcongr
    _ = (delta : ENNReal) ^ (-outerEpsilon) *
          (delta : ENNReal) ^ (-2 * gamma) *
            actualVolume ^ (1 - gamma / 2) := by
      calc
        (delta : ENNReal) ^ (-(outerEpsilon - innerEpsilon)) *
              ((delta : ENNReal) ^ (-innerEpsilon) *
                (delta : ENNReal) ^ (-2 * gamma) *
                  actualVolume ^ (1 - gamma / 2)) =
            ((delta : ENNReal) ^ (-(outerEpsilon - innerEpsilon)) *
              (delta : ENNReal) ^ (-innerEpsilon)) *
                (delta : ENNReal) ^ (-2 * gamma) *
                  actualVolume ^ (1 - gamma / 2) := by ac_rfl
        _ = (delta : ENNReal) ^ (-outerEpsilon) *
              (delta : ENNReal) ^ (-2 * gamma) *
                actualVolume ^ (1 - gamma / 2) := by rw [hpow]

/-- Restriction monotonicity plus fixed-loss absorption transports the
selected-family RHS to the source-family volume. -/
theorem fixedLoss_mul_selected_frostmanMultiplicityRHS_le_source
    {delta : NNReal} {selectedVolume sourceVolume loss : ENNReal}
    {innerEpsilon outerEpsilon gamma : Real}
    (hdelta : 0 < delta) (hlossTop : loss ≠ ∞)
    (hgap : innerEpsilon < outerEpsilon) (hgamma : gamma ≤ 2)
    (hvolume : selectedVolume ≤ sourceVolume)
    (hsmall : delta ≤
      fixedLossFrostmanRHSThreshold loss innerEpsilon outerEpsilon) :
    loss * frostmanMultiplicityRHS delta selectedVolume innerEpsilon gamma ≤
      frostmanMultiplicityRHS delta sourceVolume outerEpsilon gamma := by
  have hvolumeRHS :
      frostmanMultiplicityRHS delta selectedVolume innerEpsilon gamma ≤
        frostmanMultiplicityRHS delta sourceVolume innerEpsilon gamma := by
    have h := frostmanMultiplicityRHS_le_of_volume_le_factor_mul
      (delta := delta) (selectedVolume := selectedVolume)
      (sourceVolume := sourceVolume) (factor := (1 : ENNReal))
      (epsilon := innerEpsilon) (gamma := gamma) hgamma (by simpa using hvolume)
    simpa using h
  calc
    loss * frostmanMultiplicityRHS delta selectedVolume innerEpsilon gamma ≤
        loss * frostmanMultiplicityRHS delta sourceVolume innerEpsilon gamma := by
      gcongr
    _ ≤ frostmanMultiplicityRHS delta sourceVolume outerEpsilon gamma :=
      fixedLoss_mul_frostmanMultiplicityRHS_le
        hdelta hlossTop hgap hsmall

/-- Consumer form used by a constant-loss restriction theorem. -/
theorem source_averageMultiplicity_le_of_fixedLoss_selectedRHS
    {delta : NNReal} {selectedVolume sourceVolume loss sourceAverage : ENNReal}
    {innerEpsilon outerEpsilon gamma : Real}
    (hdelta : 0 < delta) (hlossTop : loss ≠ ∞)
    (hgap : innerEpsilon < outerEpsilon) (hgamma : gamma ≤ 2)
    (hvolume : selectedVolume ≤ sourceVolume)
    (hsmall : delta ≤
      fixedLossFrostmanRHSThreshold loss innerEpsilon outerEpsilon)
    (hselected : sourceAverage ≤
      loss * frostmanMultiplicityRHS delta selectedVolume innerEpsilon gamma) :
    sourceAverage ≤
      frostmanMultiplicityRHS delta sourceVolume outerEpsilon gamma :=
  hselected.trans
    (fixedLoss_mul_selected_frostmanMultiplicityRHS_le_source
      hdelta hlossTop hgap hgamma hvolume hsmall)

#print axioms fixedLossFrostmanRHSThreshold_pos
#print axioms fixedLossFrostmanRHSThreshold_le_one
#print axioms fixedLoss_mul_frostmanMultiplicityRHS_le
#print axioms fixedLoss_mul_selected_frostmanMultiplicityRHS_le_source
#print axioms source_averageMultiplicity_le_of_fixedLoss_selectedRHS

end
end Family8FixedLossFrostmanRHSSmallDeltaV3
