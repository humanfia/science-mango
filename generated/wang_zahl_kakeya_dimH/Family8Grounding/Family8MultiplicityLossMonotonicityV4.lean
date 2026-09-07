import Family8Grounding.Family8GeneralizedScaleTrivialBranchV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8MultiplicityLossMonotonicityV4

open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedScalePropertiesV1
open Family8GeneralizedScaleTrivialBranchV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Monotonicity in the displayed multiplicity loss

On every scale at most one, increasing `epsilon` enlarges the factor
`scale ^ (-epsilon)`.  The nontrivial relative-scale branch also has an
epsilon-dependent threshold; positive losses make that threshold monotone
in the required direction.

V1--V3 are earlier API-inference drafts and are not imported here.
-/

theorem coe_rpow_neg_mono_loss
    {scale : NNReal} {epsilonSmall epsilonLarge : Real}
    (hscaleOne : scale <= 1)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    (scale : ENNReal) ^ (-epsilonSmall) <=
      (scale : ENNReal) ^ (-epsilonLarge) := by
  have hscaleOneENN : (scale : ENNReal) <= 1 := by
    exact_mod_cast hscaleOne
  exact ENNReal.rpow_le_rpow_of_exponent_ge hscaleOneENN (by linarith)

theorem katzTaoMultiplicityRHS_mono_epsilon
    {delta : NNReal} {tubeCount : Nat}
    {epsilonSmall epsilonLarge beta : Real}
    (hdeltaOne : delta <= 1)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    katzTaoMultiplicityRHS delta tubeCount epsilonSmall beta <=
      katzTaoMultiplicityRHS delta tubeCount epsilonLarge beta := by
  unfold katzTaoMultiplicityRHS
  exact mul_le_mul_left
    (coe_rpow_neg_mono_loss hdeltaOne hepsilon) _

theorem frostmanMultiplicityRHS_mono_epsilon
    {delta : NNReal} {actualVolume : ENNReal}
    {epsilonSmall epsilonLarge beta : Real}
    (hdeltaOne : delta <= 1)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    frostmanMultiplicityRHS delta actualVolume epsilonSmall beta <=
      frostmanMultiplicityRHS delta actualVolume epsilonLarge beta := by
  unfold frostmanMultiplicityRHS
  exact mul_le_mul_left
    (mul_le_mul_left
      (coe_rpow_neg_mono_loss hdeltaOne hepsilon) _) _

theorem frostmanRelativeScaleMultiplicityRHS_mono_epsilon
    {delta tau : NNReal} {actualVolume : ENNReal}
    {epsilonSmall epsilonLarge beta : Real}
    (htauOne : tau <= 1)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    frostmanRelativeScaleMultiplicityRHS
        delta tau actualVolume epsilonSmall beta <=
      frostmanRelativeScaleMultiplicityRHS
        delta tau actualVolume epsilonLarge beta := by
  unfold frostmanRelativeScaleMultiplicityRHS
  exact mul_le_mul_left
    (mul_le_mul_left
      (coe_rpow_neg_mono_loss htauOne hepsilon) _) _

theorem katzTaoAtParameters_of_epsilon_le
    {beta epsilonSmall epsilonLarge eta : Real} {delta0 : NNReal}
    (h : KatzTaoAtParameters beta epsilonSmall eta delta0)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    KatzTaoAtParameters beta epsilonLarge eta delta0 := by
  intro delta index _ _ D hD hdelta hHypotheses
  exact (h delta index D hD hdelta hHypotheses).trans
    (katzTaoMultiplicityRHS_mono_epsilon
      (hD.delta_le_half.trans (by norm_num)) hepsilon)

theorem frostmanAtParameters_of_epsilon_le
    {beta epsilonSmall epsilonLarge eta : Real} {delta0 : NNReal}
    (h : FrostmanAtParameters beta epsilonSmall eta delta0)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    FrostmanAtParameters beta epsilonLarge eta delta0 := by
  intro delta index _ _ D hD hdelta hHypotheses
  exact (h delta index D hD hdelta hHypotheses).trans
    (frostmanMultiplicityRHS_mono_epsilon
      (hD.delta_le_half.trans (by norm_num)) hepsilon)

theorem nontrivialThreshold_mono_epsilon
    {delta tau : NNReal} {epsilonSmall epsilonLarge : Real}
    (hdeltaOne : delta <= 1)
    (hepsilonSmall : 0 < epsilonSmall)
    (hepsilon : epsilonSmall <= epsilonLarge)
    (hthreshold :
      (delta : ENNReal) ^ (100 / epsilonLarge) < (tau : ENNReal)) :
    (delta : ENNReal) ^ (100 / epsilonSmall) < (tau : ENNReal) := by
  have hinverse : 1 / epsilonLarge <= 1 / epsilonSmall :=
    one_div_le_one_div_of_le hepsilonSmall hepsilon
  have hexponent : 100 / epsilonLarge <= 100 / epsilonSmall := by
    calc
      100 / epsilonLarge = 100 * (1 / epsilonLarge) := by ring
      _ <= 100 * (1 / epsilonSmall) :=
        mul_le_mul_of_nonneg_left hinverse (by norm_num)
      _ = 100 / epsilonSmall := by ring
  have hdeltaOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOne
  exact (ENNReal.rpow_le_rpow_of_exponent_ge
    hdeltaOneENN hexponent).trans_lt hthreshold

theorem katzTaoAtNontrivialRelativeScaleParameters_of_epsilon_le
    {beta epsilonSmall epsilonLarge eta : Real} {delta0 : NNReal}
    (h : KatzTaoAtNontrivialRelativeScaleParameters
      beta epsilonSmall eta delta0)
    (hepsilonSmall : 0 < epsilonSmall)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    KatzTaoAtNontrivialRelativeScaleParameters
      beta epsilonLarge eta delta0 := by
  intro delta tau index _ _ D hD hdelta htau htauDelta
    hthreshold hHypotheses
  have hthresholdSmall := nontrivialThreshold_mono_epsilon
    (delta := delta) (tau := tau)
    (hD.delta_le_half.trans (by norm_num))
    hepsilonSmall hepsilon hthreshold
  exact (h delta tau index D hD hdelta htau htauDelta
      hthresholdSmall hHypotheses).trans
    (katzTaoMultiplicityRHS_mono_epsilon
      (htauDelta.trans (hD.delta_le_half.trans (by norm_num))) hepsilon)

theorem frostmanAtNontrivialRelativeScaleParameters_of_epsilon_le
    {beta epsilonSmall epsilonLarge eta : Real} {delta0 : NNReal}
    (h : FrostmanAtNontrivialRelativeScaleParameters
      beta epsilonSmall eta delta0)
    (hepsilonSmall : 0 < epsilonSmall)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    FrostmanAtNontrivialRelativeScaleParameters
      beta epsilonLarge eta delta0 := by
  intro delta tau index _ _ D hD hdelta htau htauDelta
    hthreshold hHypotheses
  have hthresholdSmall := nontrivialThreshold_mono_epsilon
    (delta := delta) (tau := tau)
    (hD.delta_le_half.trans (by norm_num))
    hepsilonSmall hepsilon hthreshold
  exact (h delta tau index D hD hdelta htau htauDelta
      hthresholdSmall hHypotheses).trans
    (frostmanRelativeScaleMultiplicityRHS_mono_epsilon
      (htauDelta.trans (hD.delta_le_half.trans (by norm_num))) hepsilon)

theorem katzTaoAtRelativeScaleParameters_of_epsilon_le
    {beta epsilonSmall epsilonLarge eta : Real} {delta0 : NNReal}
    (h : KatzTaoAtRelativeScaleParameters
      beta epsilonSmall eta delta0)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    KatzTaoAtRelativeScaleParameters beta epsilonLarge eta delta0 := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hHypotheses
  exact (h delta tau index D hD hdelta htau htauDelta hHypotheses).trans
    (katzTaoMultiplicityRHS_mono_epsilon
      (htauDelta.trans (hD.delta_le_half.trans (by norm_num))) hepsilon)

theorem frostmanAtRelativeScaleParameters_of_epsilon_le
    {beta epsilonSmall epsilonLarge eta : Real} {delta0 : NNReal}
    (h : FrostmanAtRelativeScaleParameters
      beta epsilonSmall eta delta0)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    FrostmanAtRelativeScaleParameters beta epsilonLarge eta delta0 := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hHypotheses
  exact (h delta tau index D hD hdelta htau htauDelta hHypotheses).trans
    (frostmanRelativeScaleMultiplicityRHS_mono_epsilon
      (htauDelta.trans (hD.delta_le_half.trans (by norm_num))) hepsilon)

#print axioms coe_rpow_neg_mono_loss
#print axioms katzTaoMultiplicityRHS_mono_epsilon
#print axioms frostmanMultiplicityRHS_mono_epsilon
#print axioms frostmanRelativeScaleMultiplicityRHS_mono_epsilon
#print axioms katzTaoAtParameters_of_epsilon_le
#print axioms frostmanAtParameters_of_epsilon_le
#print axioms nontrivialThreshold_mono_epsilon
#print axioms katzTaoAtNontrivialRelativeScaleParameters_of_epsilon_le
#print axioms frostmanAtNontrivialRelativeScaleParameters_of_epsilon_le
#print axioms katzTaoAtRelativeScaleParameters_of_epsilon_le
#print axioms frostmanAtRelativeScaleParameters_of_epsilon_le

end

end Family8MultiplicityLossMonotonicityV4
