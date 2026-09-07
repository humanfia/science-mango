import Family8Grounding.Family8ThreeScaleActualFrostmanFactorAbsorptionV2
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8ThreeScaleFrostmanFactorCountLossV1

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8MultiplicityLossMonotonicityV4
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8FixedLossFrostmanRHSSmallDeltaV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# Honest count loss in the three-scale Frostman product

A literal dyadically uniform decomposition generally supplies only

`firstCount * (middleCount * thirdCount) <= countLoss * totalCount`,

not an exact product formula.  The resulting loss in the Section 8
Frostman factor is exactly `countLoss ^ (1 - gamma / 2)`.  The fixed
actual-tube-volume constant is still absorbed by the existing uniform
small-scale threshold, independently of `countLoss`.
-/

/-- Monotonicity of one Section 8 scale-count factor under an honest
multiplicative comparison of tube counts. -/
theorem sectionEightScaleCountFrostmanFactor_le_countLoss_mul
    {fine coarse : NNReal} {approxCount totalCount : Nat}
    {countLoss : ENNReal} {gamma : Real}
    (hfine : 0 < fine) (hcoarse : 0 < coarse)
    (hgammaTwo : gamma <= 2)
    (hcount : (approxCount : ENNReal) <=
      countLoss * (totalCount : ENNReal)) :
    sectionEightScaleCountFrostmanFactor
        fine coarse approxCount gamma <=
      countLoss ^ (1 - gamma / 2) *
        sectionEightScaleCountFrostmanFactor
          fine coarse totalCount gamma := by
  have hq : 0 <= 1 - gamma / 2 := by
    linarith
  have hcountPow := ENNReal.rpow_le_rpow hcount hq
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq] at hcountPow
  rw [sectionEightScaleCountFrostmanFactor_eq
      hfine hcoarse hgammaTwo,
    sectionEightScaleCountFrostmanFactor_eq
      hfine hcoarse hgammaTwo]
  calc
    (((fine : ENNReal) / (coarse : ENNReal)) ^
          (-2 * gamma + 2 * (1 - gamma / 2))) *
        (approxCount : ENNReal) ^ (1 - gamma / 2) <=
      (((fine : ENNReal) / (coarse : ENNReal)) ^
          (-2 * gamma + 2 * (1 - gamma / 2))) *
        (countLoss ^ (1 - gamma / 2) *
          (totalCount : ENNReal) ^ (1 - gamma / 2)) :=
      mul_le_mul' le_rfl hcountPow
    _ = countLoss ^ (1 - gamma / 2) *
        ((((fine : ENNReal) / (coarse : ENNReal)) ^
            (-2 * gamma + 2 * (1 - gamma / 2))) *
          (totalCount : ENNReal) ^ (1 - gamma / 2)) := by
      ac_rfl

/-- The official three relative-scale factors telescope with the exact
uniform-count loss forced by a one-sided cardinality comparison. -/
theorem sectionEight_threeScale_factors_le_countLoss_mul_source
    {delta tau theta : NNReal}
    {firstCount middleCount thirdCount totalCount : Nat}
    {countLoss : ENNReal} {gamma : Real}
    (hdelta : 0 < delta) (htau : 0 < tau) (htheta : 0 < theta)
    (hgammaTwo : gamma <= 2)
    (hcount :
      ((firstCount * (middleCount * thirdCount) : Nat) : ENNReal) <=
        countLoss * (totalCount : ENNReal)) :
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) <=
      countLoss ^ (1 - gamma / 2) *
        sectionEightScaleCountFrostmanFactor
          delta 1 totalCount gamma := by
  calc
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) =
      sectionEightScaleCountFrostmanFactor delta 1
        (firstCount * (middleCount * thirdCount)) gamma :=
      sectionEight_threeScale_factors_eq_source
        hdelta htau htheta hgammaTwo rfl
    _ <= countLoss ^ (1 - gamma / 2) *
        sectionEightScaleCountFrostmanFactor delta 1 totalCount gamma :=
      sectionEightScaleCountFrostmanFactor_le_countLoss_mul
        hdelta (by norm_num) hgammaTwo hcount

/-- Before fixed-constant absorption, the only losses are the honest count
loss and the explicit actual tube-volume constant two. -/
theorem sectionEight_threeScale_factors_le_countLoss_mul_two_mul_actualRHS
    {delta tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {firstCount middleCount thirdCount : Nat}
    {countLoss : ENNReal} {epsilon gamma : Real}
    (htau : 0 < tau) (htheta : 0 < theta)
    (hepsilon : 0 <= epsilon) (hgammaTwo : gamma <= 2)
    (hcount :
      ((firstCount * (middleCount * thirdCount) : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal)) :
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) <=
      (countLoss ^ (1 - gamma / 2) *
          (2 : ENNReal) ^ (1 - gamma / 2)) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume epsilon gamma := by
  have hdeltaOne : delta <= 1 :=
    hD.delta_le_half.trans (by norm_num)
  calc
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) <=
      countLoss ^ (1 - gamma / 2) *
        sectionEightScaleCountFrostmanFactor
          delta 1 (Fintype.card index) gamma :=
      sectionEight_threeScale_factors_le_countLoss_mul_source
        hD.delta_pos htau htheta hgammaTwo hcount
    _ = countLoss ^ (1 - gamma / 2) *
        frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta (Fintype.card index))
          0 gamma := by
      rw [sectionEightScaleCountFrostmanFactor_to_one_eq_rhs_zero]
    _ <= countLoss ^ (1 - gamma / 2) *
        frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta (Fintype.card index))
          epsilon gamma := by
      exact mul_le_mul' le_rfl
        (frostmanMultiplicityRHS_mono_epsilon hdeltaOne hepsilon)
    _ <= countLoss ^ (1 - gamma / 2) *
        (frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon gamma *
          (2 : ENNReal) ^ (1 - gamma / 2)) := by
      exact mul_le_mul' le_rfl
        (frostmanMultiplicityRHS_cardScale_le_actual_mul_two_rpow
          D hD.delta_le_half hgammaTwo)
    _ = (countLoss ^ (1 - gamma / 2) *
          (2 : ENNReal) ^ (1 - gamma / 2)) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume epsilon gamma := by
      ac_rfl

/-- The fixed volume-normalization constant is absorbed independently of
the possibly scale-dependent uniform-count loss. -/
theorem sectionEight_threeScale_factors_le_countLoss_mul_actualRHS
    {delta tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {firstCount middleCount thirdCount : Nat}
    {countLoss : ENNReal} {epsilon gamma : Real}
    (htau : 0 < tau) (htheta : 0 < theta)
    (hepsilon : 0 < epsilon) (hgammaTwo : gamma <= 2)
    (hcount :
      ((firstCount * (middleCount * thirdCount) : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal))
    (hsmall : delta <=
      sectionEightThreeScaleActualThreshold gamma epsilon) :
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) <=
      countLoss ^ (1 - gamma / 2) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume epsilon gamma := by
  have hconstantTop :
      (2 : ENNReal) ^ (1 - gamma / 2) ≠ (⊤ : ENNReal) := by
    exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  calc
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) <=
      (countLoss ^ (1 - gamma / 2) *
          (2 : ENNReal) ^ (1 - gamma / 2)) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume 0 gamma :=
      sectionEight_threeScale_factors_le_countLoss_mul_two_mul_actualRHS
        D hD htau htheta (by norm_num) hgammaTwo hcount
    _ = countLoss ^ (1 - gamma / 2) *
        ((2 : ENNReal) ^ (1 - gamma / 2) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume 0 gamma) := by
      ac_rfl
    _ <= countLoss ^ (1 - gamma / 2) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume epsilon gamma := by
      exact mul_le_mul' le_rfl
        (fixedLoss_mul_frostmanMultiplicityRHS_le
          hD.delta_pos hconstantTop hepsilon hsmall)

#print axioms sectionEightScaleCountFrostmanFactor_le_countLoss_mul
#print axioms sectionEight_threeScale_factors_le_countLoss_mul_source
#print axioms
  sectionEight_threeScale_factors_le_countLoss_mul_two_mul_actualRHS
#print axioms sectionEight_threeScale_factors_le_countLoss_mul_actualRHS

end

end Family8ThreeScaleFrostmanFactorCountLossV1
