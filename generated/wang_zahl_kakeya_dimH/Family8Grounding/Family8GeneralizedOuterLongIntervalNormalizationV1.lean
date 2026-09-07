import Family8Grounding.Family8ExplicitConcentrationFreshReturnNormalizationV2
import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8GeneralizedOuterLongIntervalNormalizationV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ExplicitConcentrationFreshReturnNormalizationV2

noncomputable section

/-!
# Normalize a generalized coarse-scale outer bound to the long scale

The generalized outer theorem has two extra factors relative to the paper's
ordinary Katz--Tao expression: a coarse-scale loss and a coefficient to the
power `1 - beta`.  This module transports both to the global scale and
records the exact exponent budget.  A successor also absorbs the honest
factor eight introduced by the canonical B2 normalization.
-/

theorem generalizedKatzTaoMultiplicityRHS_coarse_le_global
    {d b : NNReal} {C : ENNReal} {tubeCount : Nat}
    {coarseEta coefficientEta targetEta beta : Real}
    (hd : 0 < d) (hdOne : d <= 1) (hdb : d <= b)
    (hcoarseEta : 0 <= coarseEta) (hbeta1 : beta <= 1)
    (hCpower : C <= (d : ENNReal) ^ (-coefficientEta))
    (hbudget : coarseEta + coefficientEta * (1 - beta) <= targetEta) :
    generalizedKatzTaoMultiplicityRHS b C tubeCount coarseEta beta <=
      katzTaoMultiplicityRHS d tubeCount targetEta beta := by
  let dE : ENNReal := (d : ENNReal)
  let bE : ENNReal := (b : ENNReal)
  let nE : ENNReal := (tubeCount : ENNReal)
  have hb : 0 < b := hd.trans_le hdb
  have hbaseNN : b ^ (-coarseEta) <= d ^ (-coarseEta) :=
    NNReal.rpow_le_rpow_of_nonpos hd hdb (neg_nonpos.mpr hcoarseEta)
  have hbase : bE ^ (-coarseEta) <= dE ^ (-coarseEta) := by
    dsimp only [bE, dE]
    rw [← ENNReal.coe_rpow_of_ne_zero hb.ne' (-coarseEta),
      ← ENNReal.coe_rpow_of_ne_zero hd.ne' (-coarseEta)]
    exact ENNReal.coe_le_coe.mpr hbaseNN
  have hcoefficient : C ^ (1 - beta) <=
      (dE ^ (-coefficientEta)) ^ (1 - beta) :=
    ENNReal.rpow_le_rpow hCpower (sub_nonneg.mpr hbeta1)
  have hd0 : dE ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hdTop : dE ≠ ∞ := ENNReal.coe_ne_top
  have hpowers :
      dE ^ (-coarseEta) *
          (dE ^ (-coefficientEta)) ^ (1 - beta) =
        dE ^ (-(coarseEta + coefficientEta * (1 - beta))) := by
    rw [← ENNReal.rpow_mul,
      ← ENNReal.rpow_add _ _ hd0 hdTop]
    congr 1
    ring
  have hdOneENN : dE <= 1 := by
    dsimp only [dE]
    exact ENNReal.coe_le_coe.mpr hdOne
  have htarget :
      dE ^ (-(coarseEta + coefficientEta * (1 - beta))) <=
        dE ^ (-targetEta) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN
    linarith
  unfold generalizedKatzTaoMultiplicityRHS katzTaoMultiplicityRHS
  change bE ^ (-coarseEta) * C ^ (1 - beta) * nE ^ beta <=
    dE ^ (-targetEta) * nE ^ beta
  calc
    bE ^ (-coarseEta) * C ^ (1 - beta) * nE ^ beta <=
        dE ^ (-coarseEta) *
          (dE ^ (-coefficientEta)) ^ (1 - beta) * nE ^ beta :=
      mul_le_mul' (mul_le_mul' hbase hcoefficient) le_rfl
    _ = dE ^ (-(coarseEta + coefficientEta * (1 - beta))) *
        nE ^ beta := by rw [hpowers]
    _ <= dE ^ (-targetEta) * nE ^ beta :=
      mul_le_mul' htarget le_rfl

theorem generalizedKatzTaoMultiplicityRHS_div_eight_le_global
    {d b : NNReal} {C : ENNReal} {tubeCount : Nat}
    {coarseEta scaleAbsorbEta coefficientEta targetEta beta : Real}
    (hd : 0 < d) (hdOne : d <= 1) (hdb : d <= b)
    (hcoarseEta : 0 <= coarseEta)
    (hscaleAbsorbEta : 0 < scaleAbsorbEta)
    (hbeta1 : beta <= 1)
    (hscaleSmall : b <=
      explicitConcentrationFreshReturnScaleThreshold
        coarseEta scaleAbsorbEta)
    (hCpower : C <= (d : ENNReal) ^ (-coefficientEta))
    (hbudget :
      coarseEta + scaleAbsorbEta + coefficientEta * (1 - beta) <=
        targetEta) :
    generalizedKatzTaoMultiplicityRHS (b / 8) C tubeCount
        coarseEta beta <=
      katzTaoMultiplicityRHS d tubeCount targetEta beta := by
  have hb : 0 < b := hd.trans_le hdb
  have hnormalized :
      generalizedKatzTaoMultiplicityRHS (b / 8) C tubeCount
          coarseEta beta <=
        generalizedKatzTaoMultiplicityRHS b C tubeCount
          (coarseEta + scaleAbsorbEta) beta := by
    have h := loss_mul_generalizedKatzTaoMultiplicityRHS_div_eight_le
      (delta := b) (C := C) (L := (1 : ENNReal))
      (tubeCount := tubeCount) (epsilon := coarseEta)
      (lossEta := 0) (scaleAbsorbEta := scaleAbsorbEta) (beta := beta)
      hb (by simp) hscaleAbsorbEta hscaleSmall
    simpa only [one_mul, zero_add, add_zero] using h
  exact hnormalized.trans
    (generalizedKatzTaoMultiplicityRHS_coarse_le_global
      hd hdOne hdb (by linarith) hbeta1 hCpower (by linarith))

#print axioms generalizedKatzTaoMultiplicityRHS_coarse_le_global
#print axioms generalizedKatzTaoMultiplicityRHS_div_eight_le_global

end
end Family8GeneralizedOuterLongIntervalNormalizationV1
