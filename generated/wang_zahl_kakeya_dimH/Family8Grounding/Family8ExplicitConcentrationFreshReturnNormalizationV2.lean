import Family8Grounding.Family8GeneralizedKatzTaoSamplingNumericsV1
import Family8Grounding.Family8ExplicitConcentrationFreshPowerBudgetsV4
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8ExplicitConcentrationFreshReturnNormalizationV2

open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedKatzTaoSamplingNumericsV1
open Family8ExplicitConcentrationFreshPowerBudgetsV4
open Family8ScaleContainedB2FreshKatzTaoEndpointV1
open Family8FrostmanRHSScaleVolumeAlgebraV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Returning the sampled fresh bound to generalized Katz--Tao

V1 is a failed rewrite/namespace draft and is intentionally not imported.
-/

def explicitConcentrationFreshReturnLossConstant : ENNReal :=
  480000 * 128 + 2

def explicitConcentrationFreshReturnLossThreshold
    (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    explicitConcentrationFreshReturnLossConstant absorbEta

theorem explicitConcentrationFreshReturnLossConstant_ne_top :
    explicitConcentrationFreshReturnLossConstant ≠ ∞ := by
  norm_num [explicitConcentrationFreshReturnLossConstant]

theorem explicitConcentrationFreshReturnLossThreshold_pos
    (absorbEta : Real) :
    0 < explicitConcentrationFreshReturnLossThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem sourceKatzTaoFreshLoss_coe_le_delta_negativePower
    {delta : NNReal} {Csample : ENNReal}
    {sampleEta absorbEta : Real}
    (hdelta : 0 < delta)
    (hCfinite : Csample ≠ ∞) (hCone : 1 ≤ Csample)
    (hCpower : Csample ≤ (delta : ENNReal) ^ (-sampleEta))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta ≤
      explicitConcentrationFreshReturnLossThreshold absorbEta) :
    (sourceKatzTaoFreshLoss Csample : ENNReal) ≤
      (delta : ENNReal) ^ (-(sampleEta + absorbEta)) := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hloss := sourceKatzTaoFreshLoss_coe_le_fixed_mul hCfinite hCone
  have hconstant : explicitConcentrationFreshReturnLossConstant ≤
      d ^ (-absorbEta) := by
    exact finiteConstant_le_delta_negativePower
      explicitConcentrationFreshReturnLossConstant_ne_top habsorbEta hdelta
        (by simpa [explicitConcentrationFreshReturnLossThreshold] using hsmall)
  calc
    (sourceKatzTaoFreshLoss Csample : ENNReal) ≤
        explicitConcentrationFreshReturnLossConstant * Csample := by
      simpa [explicitConcentrationFreshReturnLossConstant] using hloss
    _ ≤ d ^ (-absorbEta) * d ^ (-sampleEta) :=
      mul_le_mul' hconstant hCpower
    _ = d ^ ((-absorbEta) + (-sampleEta)) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = d ^ (-(sampleEta + absorbEta)) := by
      congr 1
      ring

def explicitConcentrationFreshReturnScaleConstant
    (epsilon : Real) : ENNReal :=
  (8 : ENNReal) ^ epsilon

def explicitConcentrationFreshReturnScaleThreshold
    (epsilon absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (explicitConcentrationFreshReturnScaleConstant epsilon) absorbEta

theorem explicitConcentrationFreshReturnScaleConstant_ne_top
    (epsilon : Real) :
    explicitConcentrationFreshReturnScaleConstant epsilon ≠ ∞ := by
  unfold explicitConcentrationFreshReturnScaleConstant
  exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)

theorem explicitConcentrationFreshReturnScaleThreshold_pos
    (epsilon absorbEta : Real) :
    0 < explicitConcentrationFreshReturnScaleThreshold epsilon absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem generalizedKatzTaoMultiplicityRHS_div_eight
    (delta : NNReal) (C : ENNReal) (tubeCount : Nat)
    (epsilon beta : Real) :
    generalizedKatzTaoMultiplicityRHS (delta / 8) C tubeCount epsilon beta =
      (8 : ENNReal) ^ epsilon *
        generalizedKatzTaoMultiplicityRHS delta C tubeCount epsilon beta := by
  unfold generalizedKatzTaoMultiplicityRHS
  rw [coe_div_eight_rpow delta (-epsilon)]
  ring_nf

theorem loss_mul_generalizedKatzTaoMultiplicityRHS_div_eight_le
    {delta : NNReal} {C L : ENNReal} {tubeCount : Nat}
    {epsilon lossEta scaleAbsorbEta beta : Real}
    (hdelta : 0 < delta)
    (hL : L ≤ (delta : ENNReal) ^ (-lossEta))
    (hscaleAbsorbEta : 0 < scaleAbsorbEta)
    (hsmall : delta ≤
      explicitConcentrationFreshReturnScaleThreshold epsilon scaleAbsorbEta) :
    L * generalizedKatzTaoMultiplicityRHS
          (delta / 8) C tubeCount epsilon beta ≤
      generalizedKatzTaoMultiplicityRHS delta C tubeCount
        (epsilon + lossEta + scaleAbsorbEta) beta := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hscale : (8 : ENNReal) ^ epsilon ≤ d ^ (-scaleAbsorbEta) := by
    exact finiteConstant_le_delta_negativePower
      (explicitConcentrationFreshReturnScaleConstant_ne_top epsilon)
        hscaleAbsorbEta hdelta
        (by simpa [explicitConcentrationFreshReturnScaleThreshold,
          explicitConcentrationFreshReturnScaleConstant] using hsmall)
  have hcoefficient :
      L * (8 : ENNReal) ^ epsilon ≤
        d ^ (-(lossEta + scaleAbsorbEta)) := by
    calc
      L * (8 : ENNReal) ^ epsilon ≤
          d ^ (-lossEta) * d ^ (-scaleAbsorbEta) :=
        mul_le_mul' hL hscale
      _ = d ^ ((-lossEta) + (-scaleAbsorbEta)) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop]
      _ = d ^ (-(lossEta + scaleAbsorbEta)) := by
        congr 1
        ring
  have hpowers :
      d ^ (-(lossEta + scaleAbsorbEta)) * d ^ (-epsilon) =
        d ^ (-(epsilon + lossEta + scaleAbsorbEta)) := by
    calc
      d ^ (-(lossEta + scaleAbsorbEta)) * d ^ (-epsilon) =
          d ^ ((-(lossEta + scaleAbsorbEta)) + (-epsilon)) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop]
      _ = d ^ (-(epsilon + lossEta + scaleAbsorbEta)) := by
        congr 1
        ring
  rw [generalizedKatzTaoMultiplicityRHS_div_eight]
  unfold generalizedKatzTaoMultiplicityRHS
  calc
    L * ((8 : ENNReal) ^ epsilon *
        (d ^ (-epsilon) * C ^ (1 - beta) *
          (tubeCount : ENNReal) ^ beta)) =
      (L * (8 : ENNReal) ^ epsilon) *
        (d ^ (-epsilon) * C ^ (1 - beta) *
          (tubeCount : ENNReal) ^ beta) := by ac_rfl
    _ ≤ d ^ (-(lossEta + scaleAbsorbEta)) *
        (d ^ (-epsilon) * C ^ (1 - beta) *
          (tubeCount : ENNReal) ^ beta) :=
      mul_le_mul' hcoefficient le_rfl
    _ = d ^ (-(epsilon + lossEta + scaleAbsorbEta)) *
        C ^ (1 - beta) * (tubeCount : ENNReal) ^ beta := by
      rw [← hpowers]
      ac_rfl

theorem returnedFreshSample_le_generalizedKatzTaoMultiplicityRHS
    {delta : NNReal} {C L : ENNReal}
    {k selectedCard tubeCount : Nat}
    {epsilon cardEta cardAbsorbEta lossEta scaleAbsorbEta beta : Real}
    (hdelta : 0 < delta)
    (hk : 0 < k)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hcardAbsorbEta : 0 < cardAbsorbEta)
    (hkC : (k : ENNReal) ≤ 2 * C)
    (hscaledCard :
      (k : ENNReal) * (selectedCard : ENNReal) ≤
        (((delta / 8 : NNReal) : ENNReal) ^ (-cardEta)) *
          (tubeCount : ENNReal))
    (hcardSmall : delta / 8 ≤
      finiteConstantSmallDeltaThreshold 4 cardAbsorbEta)
    (hL : L ≤ (delta : ENNReal) ^ (-lossEta))
    (hscaleAbsorbEta : 0 < scaleAbsorbEta)
    (hscaleSmall : delta ≤
      explicitConcentrationFreshReturnScaleThreshold
        (epsilon + beta * cardEta + cardAbsorbEta) scaleAbsorbEta) :
    ((2 * k : Nat) : ENNReal) * L *
        katzTaoMultiplicityRHS (delta / 8) selectedCard epsilon beta ≤
      generalizedKatzTaoMultiplicityRHS delta C tubeCount
        ((epsilon + beta * cardEta + cardAbsorbEta) +
          lossEta + scaleAbsorbEta) beta := by
  have hdeltaEight : 0 < delta / 8 := div_pos hdelta (by norm_num)
  have hreturned :=
    returnedSample_le_generalizedKatzTaoMultiplicityRHS
      (delta := delta / 8) (C := C) (k := k)
      (sampledCard := selectedCard) (tubeCount := tubeCount)
      (epsilon := epsilon) (eta := cardEta)
      (absorbEta := cardAbsorbEta) (beta := beta)
      hdeltaEight hk hbeta0 hbeta1 hcardAbsorbEta hkC hscaledCard hcardSmall
  calc
    ((2 * k : Nat) : ENNReal) * L *
        katzTaoMultiplicityRHS (delta / 8) selectedCard epsilon beta =
      L * (((2 * k : Nat) : ENNReal) *
        katzTaoMultiplicityRHS (delta / 8) selectedCard epsilon beta) := by
      ac_rfl
    _ ≤ L * generalizedKatzTaoMultiplicityRHS (delta / 8) C tubeCount
        (epsilon + beta * cardEta + cardAbsorbEta) beta :=
      mul_le_mul' le_rfl hreturned
    _ ≤ generalizedKatzTaoMultiplicityRHS delta C tubeCount
        ((epsilon + beta * cardEta + cardAbsorbEta) +
          lossEta + scaleAbsorbEta) beta :=
      loss_mul_generalizedKatzTaoMultiplicityRHS_div_eight_le
        hdelta hL hscaleAbsorbEta hscaleSmall

#print axioms explicitConcentrationFreshReturnLossConstant_ne_top
#print axioms explicitConcentrationFreshReturnLossThreshold_pos
#print axioms sourceKatzTaoFreshLoss_coe_le_delta_negativePower
#print axioms explicitConcentrationFreshReturnScaleConstant_ne_top
#print axioms explicitConcentrationFreshReturnScaleThreshold_pos
#print axioms generalizedKatzTaoMultiplicityRHS_div_eight
#print axioms loss_mul_generalizedKatzTaoMultiplicityRHS_div_eight_le
#print axioms returnedFreshSample_le_generalizedKatzTaoMultiplicityRHS

end
end Family8ExplicitConcentrationFreshReturnNormalizationV2
