import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
import Family8Grounding.Family8KatzTaoDoubledParentConflictBudgetSideConditionsV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8ExactConflictDensityBudgetV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2
open Family8KatzTaoDoubledParentConflictBudgetSideConditionsV1
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17

noncomputable section

/-!
# Sharp conflict-degree loss in the selected density budget

The weighted selector divides source density by its exact conflict budget.
This module pays that division using the sharp power envelope for the
canonical buffered scale.  The only exponent condition is the literal room
between the source-density exponent and the target Frostman exponent.
-/

/-- Generic division-free power absorption for a density loss. -/
theorem rpow_le_density_div_of_powerLoss
    {d : NNReal} {B density : ENNReal}
    {sourceExponent targetExponent lossExponent : Real}
    (hd : 0 < d) (hdOne : d <= 1)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hB : B <= (d : ENNReal) ^ (-lossExponent))
    (hexponent : sourceExponent <= targetExponent - lossExponent)
    (hsource : (d : ENNReal) ^ sourceExponent <= density) :
    (d : ENNReal) ^ targetExponent <= density / B := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl hB0) (Or.inl hBTop)).2
  have hd0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hdTop : (d : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOneENN : (d : ENNReal) <= 1 := by exact_mod_cast hdOne
  calc
    (d : ENNReal) ^ targetExponent * B <=
        (d : ENNReal) ^ targetExponent *
          (d : ENNReal) ^ (-lossExponent) :=
      mul_le_mul' le_rfl hB
    _ = (d : ENNReal) ^ (targetExponent - lossExponent) := by
      rw [show targetExponent - lossExponent =
        targetExponent + (-lossExponent) by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (d : ENNReal) ^ sourceExponent :=
      ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN hexponent
    _ <= density := hsource

/-- At the canonical buffered scale the exact Katz--Tao conflict budget is
absorbed by its sharp power envelope, yielding the selected-density input
used by the weighted Frostman endpoint. -/
theorem canonicalLowerBufferedScale_exactConflict_densityBudget
    {tau theta : NNReal} {A density : ENNReal}
    {epsilon katzTaoExponent absorbExponent sourceExponent targetExponent : Real}
    (htau : 0 < tau) (htauTheta : tau <= theta)
    (hthetaOne : theta <= 1) (hepsilon : 0 <= epsilon)
    (habsorb : 0 < absorbExponent)
    (htauThreshold :
      tau <= activeOwnerExactDegreeSmallDeltaThreshold absorbExponent)
    (hAone : 1 <= A)
    (hA : A <= (tau : ENNReal) ^ (-katzTaoExponent))
    (hexponent : sourceExponent <= targetExponent -
      activeOwnerExactDegreePowerEnvelope
        epsilon katzTaoExponent absorbExponent)
    (hsource : (tau : ENNReal) ^ sourceExponent <= density) :
    (tau : ENNReal) ^ targetExponent <=
      density /
        katzTaoDoubledParentConflictBudget tau
          (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
            tau theta epsilon) A := by
  let B := katzTaoDoubledParentConflictBudget tau
    (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
      tau theta epsilon) A
  have hB : B <= (tau : ENNReal) ^
      (-activeOwnerExactDegreePowerEnvelope
        epsilon katzTaoExponent absorbExponent) := by
    simpa only [B, katzTaoDoubledParentConflictBudget] using
      (canonicalLowerBufferedScale_exactConflictDegree_le_powerEnvelope_auto
        (globalDelta := tau) (tau := tau) (theta := theta) (A := A)
        (epsilon := epsilon) (eta := katzTaoExponent)
        (absorbEta := absorbExponent)
        htau le_rfl htauTheta hthetaOne hepsilon habsorb
        htauThreshold hAone hA)
  exact rpow_le_density_div_of_powerLoss
    htau (htauTheta.trans hthetaOne)
    (katzTaoDoubledParentConflictBudget_ne_zero tau
      (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
        tau theta epsilon) A)
    (katzTaoDoubledParentConflictBudget_ne_top tau
      (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
        tau theta epsilon) A)
    hB hexponent hsource

/-- Frostman source specialization of the canonical sharp density budget.
No selected-density callback remains: the source-density premise is the
first field of the actual Frostman hypotheses. -/
theorem canonicalLowerBufferedScale_exactConflict_densityBudget_of_frostman
    {tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum tau index)
    {A : ENNReal}
    {epsilon katzTaoExponent absorbExponent sourceExponent targetExponent : Real}
    (hF : FrostmanHypotheses D sourceExponent)
    (htau : 0 < tau) (htauTheta : tau <= theta)
    (hthetaOne : theta <= 1) (hepsilon : 0 <= epsilon)
    (habsorb : 0 < absorbExponent)
    (htauThreshold :
      tau <= activeOwnerExactDegreeSmallDeltaThreshold absorbExponent)
    (hAone : 1 <= A)
    (hA : A <= (tau : ENNReal) ^ (-katzTaoExponent))
    (hexponent : sourceExponent <= targetExponent -
      activeOwnerExactDegreePowerEnvelope
        epsilon katzTaoExponent absorbExponent) :
    (tau : ENNReal) ^ targetExponent <=
      D.shading.shadingDensity /
        katzTaoDoubledParentConflictBudget tau
          (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
            tau theta epsilon) A := by
  exact canonicalLowerBufferedScale_exactConflict_densityBudget
    htau htauTheta hthetaOne hepsilon habsorb htauThreshold
    hAone hA hexponent hF.1

#print axioms rpow_le_density_div_of_powerLoss
#print axioms canonicalLowerBufferedScale_exactConflict_densityBudget
#print axioms
  canonicalLowerBufferedScale_exactConflict_densityBudget_of_frostman

end
end Family8ExactConflictDensityBudgetV1
