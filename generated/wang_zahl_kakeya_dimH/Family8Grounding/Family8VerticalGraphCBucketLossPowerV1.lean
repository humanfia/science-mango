import Family8Grounding.Family8Family7WeightedVerticalGraphCBucketV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8VerticalGraphCBucketLossPowerV1

open Family8Family7WeightedVerticalGraphCBucketV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# A power bound for the vertical graph-coordinate bucket loss

The graph coordinate lies in `[-2,2]`.  Thus the literal floor-grid label
set at mesh `eta` has size at most `4 / eta + 2`.  At the half-`tau` mesh,
the complete graph-selection loss `3 * card` is at most `30 / tau` when
`tau <= 1`.  One positive small power of `delta` absorbs the fixed factor
`30`, while `delta <= tau` pays the remaining inverse scale.
-/

/-- Direct numerical estimate for the literal integer floor interval. -/
theorem verticalGraphCBucketLoss_real_le_div_add_two
    {eta : Real} (heta : 0 < eta) :
    (verticalGraphCBucketLoss eta : Real) <= 4 / eta + 2 := by
  let x : Real := 2 / eta
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hfloorOrder :
      Int.floor ((-2 : Real) / eta) <=
        Int.floor ((2 : Real) / eta) := by
    apply Int.floor_mono
    exact (div_le_div_iff_of_pos_right heta).2 (by norm_num)
  have hnonneg :
      0 <= Int.floor ((2 : Real) / eta) + 1 -
        Int.floor ((-2 : Real) / eta) := by
    omega
  have htoNat :
      (((Int.floor ((2 : Real) / eta) + 1 -
          Int.floor ((-2 : Real) / eta)).toNat : Nat) : Int) =
        Int.floor ((2 : Real) / eta) + 1 -
          Int.floor ((-2 : Real) / eta) :=
    Int.toNat_of_nonneg hnonneg
  have hcast :
      (verticalGraphCBucketLoss eta : Real) =
        ((Int.floor ((2 : Real) / eta) + 1 -
          Int.floor ((-2 : Real) / eta) : Int) : Real) := by
    rw [verticalGraphCBucketLoss_eq]
    exact_mod_cast htoNat
  have hfloor : ((Int.floor x : Int) : Real) <= x := Int.floor_le x
  have hceil : ((Int.ceil x : Int) : Real) <= x + 1 :=
    (Int.ceil_lt_add_one x).le
  rw [hcast]
  have hneg : (-2 : Real) / eta = -x := by
    dsimp only [x]
    ring
  have hpos : (2 : Real) / eta = x := by rfl
  rw [hneg, hpos, Int.floor_neg]
  norm_num only [Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_one]
  calc
    (Int.floor x : Real) + 1 - -(Int.ceil x : Real) <=
        x + 1 - -(x + 1) := by gcongr
    _ = 4 / eta + 2 := by
      dsimp only [x]
      field_simp
      ring

/-- At the mesh `tau / 2`, the full factor-three graph-selection loss is
bounded by the explicit inverse-scale coefficient `30 / tau`. -/
theorem three_mul_verticalGraphCBucketLoss_halfScale_real_le
    {tau : NNReal} (htau : 0 < tau) (htauOne : tau <= 1) :
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : Real) <=
      30 / (tau : Real) := by
  have htauReal : 0 < (tau : Real) := by exact_mod_cast htau
  have htauRealOne : (tau : Real) <= 1 := by exact_mod_cast htauOne
  have hbucket := verticalGraphCBucketLoss_real_le_div_add_two
    (eta := (tau : Real) / 2) (by positivity)
  have hsix : (6 : Real) <= 6 / (tau : Real) := by
    rw [le_div_iff₀ htauReal]
    nlinarith
  calc
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : Real) =
        3 * (verticalGraphCBucketLoss ((tau : Real) / 2) : Real) := by
      norm_num
    _ <= 3 * (4 / ((tau : Real) / 2) + 2) := by gcongr
    _ = 24 / (tau : Real) + 6 := by
      field_simp
      ring
    _ <= 24 / (tau : Real) + 6 / (tau : Real) := by gcongr
    _ = 30 / (tau : Real) := by ring

/-- `ENNReal` form of the explicit half-scale estimate. -/
theorem three_mul_verticalGraphCBucketLoss_halfScale_le
    {tau : NNReal} (htau : 0 < tau) (htauOne : tau <= 1) :
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal) <=
      30 * (tau : ENNReal) ^ (-1 : Real) := by
  have htauReal : 0 < (tau : Real) := by exact_mod_cast htau
  have hreal := three_mul_verticalGraphCBucketLoss_halfScale_real_le
    htau htauOne
  have hofReal := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_natCast] at hofReal
  rw [ENNReal.ofReal_div_of_pos htauReal] at hofReal
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal,
    div_eq_mul_inv, ENNReal.rpow_neg_one] using hofReal

/-- The fixed threshold which reserves `absorbExponent` for the constant
`30` in the graph-bucket count. -/
def verticalGraphCBucketLossSmallDeltaThreshold
    (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 30 absorbExponent

theorem verticalGraphCBucketLossSmallDeltaThreshold_pos
    (absorbExponent : Real) :
    0 < verticalGraphCBucketLossSmallDeltaThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- Before small-scale absorption, the actual graph loss is at most the
fixed coefficient `30` times the inverse source scale. -/
theorem three_mul_verticalGraphCBucketLoss_halfScale_le_delta_inv
    {delta tau : NNReal} (hdelta : 0 < delta)
    (hdeltaTau : delta <= tau) (htauOne : tau <= 1) :
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal) <=
      30 * (delta : ENNReal) ^ (-1 : Real) := by
  have htau : 0 < tau := hdelta.trans_le hdeltaTau
  have hinvNN : tau⁻¹ <= delta⁻¹ := inv_anti₀ hdelta hdeltaTau
  have hinvENN : (tau : ENNReal)⁻¹ <= (delta : ENNReal)⁻¹ := by
    simpa only [ENNReal.coe_inv htau.ne', ENNReal.coe_inv hdelta.ne'] using
      (ENNReal.coe_le_coe.mpr hinvNN)
  calc
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal) <=
        30 * (tau : ENNReal) ^ (-1 : Real) :=
      three_mul_verticalGraphCBucketLoss_halfScale_le htau htauOne
    _ <= 30 * (delta : ENNReal) ^ (-1 : Real) := by
      simpa only [ENNReal.rpow_neg_one] using
        (mul_le_mul' (show (30 : ENNReal) <= 30 by rfl) hinvENN)

/-- Reusable absorption interface: any existing proof that the fixed factor
`30` fits in the spare `delta ^ (-absorbExponent)` budget closes the graph
loss, without committing the caller to a particular global threshold. -/
theorem three_mul_verticalGraphCBucketLoss_halfScale_le_deltaPower_of_constant
    {delta tau : NNReal} (hdelta : 0 < delta)
    (hdeltaTau : delta <= tau) (htauOne : tau <= 1)
    {absorbExponent : Real}
    (hconstant : (30 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExponent)) :
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal) <=
      (delta : ENNReal) ^ (-(1 + absorbExponent)) := by
  have hraw := three_mul_verticalGraphCBucketLoss_halfScale_le_delta_inv
    hdelta hdeltaTau htauOne
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal) <=
        30 * (delta : ENNReal) ^ (-1 : Real) := hraw
    _ <= (delta : ENNReal) ^ (-absorbExponent) *
        (delta : ENNReal) ^ (-1 : Real) :=
      mul_le_mul' hconstant le_rfl
    _ = (delta : ENNReal) ^ ((-absorbExponent) + (-1 : Real)) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (delta : ENNReal) ^ (-(1 + absorbExponent)) := by
      congr 1
      ring

/-- The literal graph-bucket loss costs one inverse scale and an arbitrarily
small positive absorption exponent.  This is the source-delta form needed
by the Family 8 graph certificate. -/
theorem three_mul_verticalGraphCBucketLoss_halfScale_le_deltaPower
    {delta tau : NNReal} (hdelta : 0 < delta)
    (hdeltaTau : delta <= tau) (htauOne : tau <= 1)
    {absorbExponent : Real} (habsorb : 0 < absorbExponent)
    (hdeltaThreshold :
      delta <= verticalGraphCBucketLossSmallDeltaThreshold absorbExponent) :
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal) <=
      (delta : ENNReal) ^ (-(1 + absorbExponent)) := by
  have hconstant : (30 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExponent) := by
    exact finiteConstant_le_delta_negativePower (by norm_num) habsorb hdelta
      (by simpa [verticalGraphCBucketLossSmallDeltaThreshold] using
        hdeltaThreshold)
  exact
    three_mul_verticalGraphCBucketLoss_halfScale_le_deltaPower_of_constant
      hdelta hdeltaTau htauOne hconstant

#print axioms verticalGraphCBucketLoss_real_le_div_add_two
#print axioms three_mul_verticalGraphCBucketLoss_halfScale_real_le
#print axioms three_mul_verticalGraphCBucketLoss_halfScale_le
#print axioms three_mul_verticalGraphCBucketLoss_halfScale_le_delta_inv
#print axioms three_mul_verticalGraphCBucketLoss_halfScale_le_deltaPower_of_constant
#print axioms three_mul_verticalGraphCBucketLoss_halfScale_le_deltaPower

end
end Family8VerticalGraphCBucketLossPowerV1
