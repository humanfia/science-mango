import Family8Grounding.Family8Prop66AActualFamilyVolumeTransportV1
import Family8Grounding.Family8MultiplicityLossMonotonicityV4
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8ThreeScaleFrostmanFactorAlgebraV2

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8MultiplicityLossMonotonicityV4
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AActualFamilyVolumeTransportV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# Three-scale Frostman factor telescoping

The outside and middle estimates in the official Section 8 argument use the
same scale-count normalization at the three ratios `delta / tau`,
`tau / theta`, and `theta / 1`.  Under exact uniform counting these three
factors telescope to the source-scale Frostman factor.  Passing from the
paper's `delta^2 * #T` normalization to the genuine summed tube volume costs
only the explicit constant `2^(1-gamma/2)`.

This file is scalar algebra only.  It does not assert a multiplicity bound or
construct any of the three uniform families.  V1 is a failed cancellation
draft and is not imported.
-/

/-- The loss-free scale-count part of the Frostman multiplicity RHS. -/
def sectionEightScaleCountFrostmanFactor
    (fine coarse : NNReal) (tubeCount : Nat) (gamma : Real) : ENNReal :=
  (((fine : ENNReal) / (coarse : ENNReal)) ^ (-2 * gamma)) *
    (((((fine : ENNReal) / (coarse : ENNReal)) ^ (2 : Nat)) *
      (tubeCount : ENNReal)) ^ (1 - gamma / 2))

/-- Separate the scale ratio and count powers. -/
theorem sectionEightScaleCountFrostmanFactor_eq
    {fine coarse : NNReal} {tubeCount : Nat} {gamma : Real}
    (hfine : 0 < fine) (hcoarse : 0 < coarse) (hgammaTwo : gamma <= 2) :
    sectionEightScaleCountFrostmanFactor fine coarse tubeCount gamma =
      (((fine : ENNReal) / (coarse : ENNReal)) ^
        (-2 * gamma + 2 * (1 - gamma / 2))) *
        (tubeCount : ENNReal) ^ (1 - gamma / 2) := by
  let x : ENNReal := (fine : ENNReal) / (coarse : ENNReal)
  let q : Real := 1 - gamma / 2
  have hq : 0 <= q := by
    dsimp only [q]
    linarith
  have hx0 : x ≠ 0 := by
    dsimp only [x]
    exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr hfine.ne', ENNReal.coe_ne_top⟩
  have hxTop : x ≠ ⊤ := by
    dsimp only [x]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hcoarse.ne')
  have hsquareCount :
      ((x ^ (2 : Nat)) * (tubeCount : ENNReal)) ^ q =
        x ^ (2 * q) * (tubeCount : ENNReal) ^ q := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  unfold sectionEightScaleCountFrostmanFactor
  change x ^ (-2 * gamma) * ((x ^ (2 : Nat)) *
    (tubeCount : ENNReal)) ^ q = _
  rw [hsquareCount]
  calc
    x ^ (-2 * gamma) *
        (x ^ (2 * q) * (tubeCount : ENNReal) ^ q) =
      (x ^ (-2 * gamma) * x ^ (2 * q)) *
        (tubeCount : ENNReal) ^ q := by
        ac_rfl
    _ = x ^ (-2 * gamma + 2 * q) *
        (tubeCount : ENNReal) ^ q := by
      rw [ENNReal.rpow_add _ _ hx0 hxTop]

/-- The scale-count factor is multiplicative across one intermediate scale. -/
theorem sectionEightScaleCountFrostmanFactor_mul
    {fine middle coarse : NNReal} {firstCount secondCount : Nat}
    {gamma : Real}
    (hfine : 0 < fine) (hmiddle : 0 < middle) (hcoarse : 0 < coarse)
    (hgammaTwo : gamma <= 2) :
    sectionEightScaleCountFrostmanFactor
        fine middle firstCount gamma *
      sectionEightScaleCountFrostmanFactor
        middle coarse secondCount gamma =
      sectionEightScaleCountFrostmanFactor
        fine coarse (firstCount * secondCount) gamma := by
  let x : ENNReal := (fine : ENNReal) / (middle : ENNReal)
  let y : ENNReal := (middle : ENNReal) / (coarse : ENNReal)
  let z : ENNReal := (fine : ENNReal) / (coarse : ENNReal)
  let q : Real := 1 - gamma / 2
  let r : Real := -2 * gamma + 2 * q
  have hq : 0 <= q := by
    dsimp only [q]
    linarith
  have hmiddle0 : (middle : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hmiddle.ne'
  have hmiddleTop : (middle : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcoarse0 : (coarse : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hcoarse.ne'
  have hxTop : x ≠ ⊤ := by
    dsimp only [x]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top hmiddle0
  have hyTop : y ≠ ⊤ := by
    dsimp only [y]
    exact ENNReal.div_ne_top hmiddleTop hcoarse0
  have hratio : x * y = z := by
    dsimp only [x, y, z]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    calc
      (fine : ENNReal) * (middle : ENNReal)⁻¹ *
          ((middle : ENNReal) * (coarse : ENNReal)⁻¹) =
        (fine : ENNReal) *
          ((middle : ENNReal)⁻¹ * (middle : ENNReal)) *
            (coarse : ENNReal)⁻¹ := by
        ac_rfl
      _ = (fine : ENNReal) * (coarse : ENNReal)⁻¹ := by
        rw [ENNReal.inv_mul_cancel hmiddle0 hmiddleTop]
        simp
  rw [sectionEightScaleCountFrostmanFactor_eq
      hfine hmiddle hgammaTwo,
    sectionEightScaleCountFrostmanFactor_eq
      hmiddle hcoarse hgammaTwo,
    sectionEightScaleCountFrostmanFactor_eq
      hfine hcoarse hgammaTwo]
  change (x ^ r * (firstCount : ENNReal) ^ q) *
      (y ^ r * (secondCount : ENNReal) ^ q) =
    z ^ r * ((firstCount * secondCount : Nat) : ENNReal) ^ q
  calc
    (x ^ r * (firstCount : ENNReal) ^ q) *
        (y ^ r * (secondCount : ENNReal) ^ q) =
      (x ^ r * y ^ r) *
        ((firstCount : ENNReal) ^ q * (secondCount : ENNReal) ^ q) := by
      ac_rfl
    _ = (x * y) ^ r *
        ((firstCount : ENNReal) * (secondCount : ENNReal)) ^ q := by
      rw [ENNReal.mul_rpow_of_ne_top hxTop hyTop,
        ENNReal.mul_rpow_of_nonneg _ _ hq]
    _ = z ^ r * ((firstCount * secondCount : Nat) : ENNReal) ^ q := by
      rw [hratio, Nat.cast_mul]

/-- The official outer-middle-outer product telescopes to the source scale. -/
theorem sectionEight_threeScale_factors_eq_source
    {delta tau theta : NNReal}
    {firstCount middleCount thirdCount totalCount : Nat}
    {gamma : Real}
    (hdelta : 0 < delta) (htau : 0 < tau) (htheta : 0 < theta)
    (hgammaTwo : gamma <= 2)
    (hcount : totalCount = firstCount * (middleCount * thirdCount)) :
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) =
      sectionEightScaleCountFrostmanFactor delta 1 totalCount gamma := by
  calc
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) =
      sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        sectionEightScaleCountFrostmanFactor
          tau 1 (middleCount * thirdCount) gamma := by
      rw [sectionEightScaleCountFrostmanFactor_mul
        htau htheta (by norm_num) hgammaTwo]
    _ = sectionEightScaleCountFrostmanFactor delta 1
        (firstCount * (middleCount * thirdCount)) gamma :=
      sectionEightScaleCountFrostmanFactor_mul
        hdelta htau (by norm_num) hgammaTwo
    _ = sectionEightScaleCountFrostmanFactor delta 1 totalCount gamma := by
      rw [hcount]

/-- At coarse scale one, the loss-free factor is the Frostman RHS with
epsilon zero and paper card-scale volume. -/
theorem sectionEightScaleCountFrostmanFactor_to_one_eq_rhs_zero
    (delta : NNReal) (tubeCount : Nat) (gamma : Real) :
    sectionEightScaleCountFrostmanFactor delta 1 tubeCount gamma =
      frostmanMultiplicityRHS delta
        (proposition66ACardScaleVolume delta tubeCount) 0 gamma := by
  simp [sectionEightScaleCountFrostmanFactor,
    frostmanMultiplicityRHS, proposition66ACardScaleVolume]

/-- Exact three-scale counting plus the honest tube-volume lower bound
recombines the three factors into the source actual-volume RHS.  The only
residual scalar is the explicit tube-volume constant two. -/
theorem sectionEight_threeScale_factors_le_two_mul_actualRHS
    {delta tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {firstCount middleCount thirdCount : Nat}
    {epsilon gamma : Real}
    (htau : 0 < tau) (htheta : 0 < theta)
    (hepsilon : 0 <= epsilon) (hgammaTwo : gamma <= 2)
    (hcount : Fintype.card index =
      firstCount * (middleCount * thirdCount)) :
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) <=
      (2 : ENNReal) ^ (1 - gamma / 2) *
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume epsilon gamma := by
  have hdeltaOne : delta <= 1 :=
    hD.delta_le_half.trans (by norm_num)
  calc
    sectionEightScaleCountFrostmanFactor delta tau firstCount gamma *
        (sectionEightScaleCountFrostmanFactor tau theta middleCount gamma *
          sectionEightScaleCountFrostmanFactor theta 1 thirdCount gamma) =
      sectionEightScaleCountFrostmanFactor
        delta 1 (Fintype.card index) gamma :=
      sectionEight_threeScale_factors_eq_source
        hD.delta_pos htau htheta hgammaTwo hcount
    _ = frostmanMultiplicityRHS delta
        (proposition66ACardScaleVolume delta (Fintype.card index)) 0 gamma :=
      sectionEightScaleCountFrostmanFactor_to_one_eq_rhs_zero
        delta (Fintype.card index) gamma
    _ <= frostmanMultiplicityRHS delta
        (proposition66ACardScaleVolume delta (Fintype.card index))
          epsilon gamma :=
      frostmanMultiplicityRHS_mono_epsilon hdeltaOne hepsilon
    _ <= frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon gamma *
        (2 : ENNReal) ^ (1 - gamma / 2) :=
      frostmanMultiplicityRHS_cardScale_le_actual_mul_two_rpow
        D hD.delta_le_half hgammaTwo
    _ = (2 : ENNReal) ^ (1 - gamma / 2) *
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon gamma := by
      ac_rfl

#print axioms sectionEightScaleCountFrostmanFactor_eq
#print axioms sectionEightScaleCountFrostmanFactor_mul
#print axioms sectionEight_threeScale_factors_eq_source
#print axioms sectionEightScaleCountFrostmanFactor_to_one_eq_rhs_zero
#print axioms sectionEight_threeScale_factors_le_two_mul_actualRHS

end

end Family8ThreeScaleFrostmanFactorAlgebraV2
