import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV11

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open scoped ENNReal NNReal

namespace Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV12

open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- A genuine scale relation converts the remaining squared scale ratio to
an `s`-negative power; the fixed geometric constant is absorbed by the
explicit small-scale threshold.  No upper bound on `s` or lower bound on the
scale exponent is needed beyond the stated scale relation. -/
theorem centeredAdaptive_fixed_mul_scaleRatio_sq_le_power
    {s delta : NNReal} (hs : 0 < s)
    {scaleExponent absorbEta : Real}
    (hscale : (s : ENNReal) ^ scaleExponent <= (delta : ENNReal))
    (habsorbEta : 0 < absorbEta)
    (hsmall : s <= centeredAdaptiveGeometricLossThreshold absorbEta) :
    centeredAdaptiveGeometricLossFixedConstant *
        (((s : ENNReal) / (delta : ENNReal)) ^ 2) <=
      (s : ENNReal) ^ (-(2 * scaleExponent - 2 + absorbEta)) := by
  let d : ENNReal := (s : ENNReal)
  let q : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hs.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdPowPos : 0 < d ^ scaleExponent :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hs) hdTop
  have hqPos : 0 < q := hdPowPos.trans_le hscale
  have hq0 : q ≠ 0 := hqPos.ne'
  have hqTop : q ≠ ∞ := ENNReal.coe_ne_top
  have hratio : d / q <= d ^ (1 - scaleExponent) := by
    apply (ENNReal.div_le_iff hq0 hqTop).2
    calc
      d = d ^ (1 - scaleExponent) * d ^ scaleExponent := by
        rw [← ENNReal.rpow_add _ _ hd0 hdTop]
        rw [show 1 - scaleExponent + scaleExponent = (1 : Real) by ring,
          ENNReal.rpow_one]
      _ <= d ^ (1 - scaleExponent) * q := by gcongr
  have hratioSq : (d / q) ^ 2 <= d ^ (2 * (1 - scaleExponent)) := by
    calc
      (d / q) ^ 2 <= (d ^ (1 - scaleExponent)) ^ 2 :=
        pow_le_pow_left' hratio 2
      _ = d ^ (2 * (1 - scaleExponent)) := by
        rw [← ENNReal.rpow_natCast (d ^ (1 - scaleExponent)) 2,
          ← ENNReal.rpow_mul]
        congr 1
        ring
  have hfixed : centeredAdaptiveGeometricLossFixedConstant <=
      d ^ (-absorbEta) := by
    exact finiteConstant_le_delta_negativePower
      centeredAdaptiveGeometricLossFixedConstant_ne_top habsorbEta hs
        (by simpa only [centeredAdaptiveGeometricLossThreshold, d] using hsmall)
  change centeredAdaptiveGeometricLossFixedConstant * (d / q) ^ 2 <=
    d ^ (-(2 * scaleExponent - 2 + absorbEta))
  calc
    centeredAdaptiveGeometricLossFixedConstant * (d / q) ^ 2 <=
        d ^ (-absorbEta) * d ^ (2 * (1 - scaleExponent)) :=
      mul_le_mul' hfixed hratioSq
    _ = d ^ ((-absorbEta) + (2 * (1 - scaleExponent))) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = d ^ (-(2 * scaleExponent - 2 + absorbEta)) := by
      congr 1
      ring

#print axioms centeredAdaptive_fixed_mul_scaleRatio_sq_le_power

end
end Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV12
