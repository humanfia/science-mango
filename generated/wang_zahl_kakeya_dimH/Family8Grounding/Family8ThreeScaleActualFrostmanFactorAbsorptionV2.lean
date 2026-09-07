import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Family8Grounding.Family8FixedLossFrostmanRHSSmallDeltaV3

open scoped ENNReal NNReal

namespace Family8ThreeScaleActualFrostmanFactorAbsorptionV2

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8FixedLossFrostmanRHSSmallDeltaV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Absorb the sole actual-volume constant in the three-scale product

Exact uniform counting telescopes the three Section 8 factors to the paper
card-scale Frostman normalization.  The genuine summed-volume endpoint costs
`2^(1-gamma/2)`.  Any positive Frostman epsilon absorbs that fixed finite
constant below the explicit threshold in this file.

V1 imported a failed legacy fixed-loss module and is not imported here.
-/

/-- Explicit terminal scale for absorbing the actual tube-volume comparison
constant into the source Frostman epsilon. -/
def sectionEightThreeScaleActualThreshold
    (gamma epsilon : Real) : NNReal :=
  fixedLossFrostmanRHSThreshold
    ((2 : ENNReal) ^ (1 - gamma / 2)) 0 epsilon

theorem sectionEightThreeScaleActualThreshold_pos
    (gamma epsilon : Real) :
    0 < sectionEightThreeScaleActualThreshold gamma epsilon :=
  fixedLossFrostmanRHSThreshold_pos _ _ _

theorem sectionEightThreeScaleActualThreshold_le_one
    (gamma : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    sectionEightThreeScaleActualThreshold gamma epsilon <= 1 :=
  fixedLossFrostmanRHSThreshold_le_one _ hepsilon

/-- The three official scale-count factors now recombine directly into the
actual source Frostman RHS.  Thus normalization is no longer a producer
field; only exact uniform count multiplication is required. -/
theorem sectionEight_threeScale_factors_le_actualRHS
    {delta tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {firstCount middleCount thirdCount : Nat}
    {epsilon gamma : Real}
    (htau : 0 < tau) (htheta : 0 < theta)
    (hepsilon : 0 < epsilon) (hgammaTwo : gamma <= 2)
    (hcount : Fintype.card index =
      firstCount * (middleCount * thirdCount))
    (hsmall : delta <=
      sectionEightThreeScaleActualThreshold gamma epsilon) :
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) <=
      frostmanMultiplicityRHS
        delta D.actualFamilyVolume epsilon gamma := by
  have hconstantTop :
      (2 : ENNReal) ^ (1 - gamma / 2) ≠ ⊤ := by
    exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  calc
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) <=
      (2 : ENNReal) ^ (1 - gamma / 2) *
        frostmanMultiplicityRHS delta D.actualFamilyVolume 0 gamma :=
      sectionEight_threeScale_factors_le_two_mul_actualRHS
        D hD htau htheta (by norm_num) hgammaTwo hcount
    _ <= frostmanMultiplicityRHS
        delta D.actualFamilyVolume epsilon gamma :=
      fixedLoss_mul_frostmanMultiplicityRHS_le
        hD.delta_pos hconstantTop hepsilon hsmall

#print axioms sectionEightThreeScaleActualThreshold_pos
#print axioms sectionEightThreeScaleActualThreshold_le_one
#print axioms sectionEight_threeScale_factors_le_actualRHS

end

end Family8ThreeScaleActualFrostmanFactorAbsorptionV2
