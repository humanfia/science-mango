import Family8Grounding.Family8Family7NativeHighAmbientPackingPowerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstNativeBranchCoreProducerV6
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighUniformCoefficientV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8Family7NativeHighAmbientCardPowerV1
open Family8Family7NativeHighAmbientPackingPowerV1
open Family8Family7NativeHighDyadicPairMassSumV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstNativeBranchCoreProducerV6
open FamilyStickyCinematicL32PyzCriticalBinUniformityV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# A datum-uniform coefficient for the genuine native-high producer

The genuine epsilon-extremal record supplies global unit-ball packing, hence
an ambient-card bound of order `radius ^ (-5)`.  This file propagates that
bound through the fourth-power native-high loss and pays the two remaining
literal dyadic-bin factors.  The result has no conclusion-valued callback
and depends only on the radius through an explicit fixed negative power.
-/

/-- A natural number is at most `2` to its own power. -/
private theorem self_le_two_pow (n : Nat) : n <= 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n + 1 <= 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ <= 2 ^ n + 2 ^ n := by
          exact Nat.add_le_add_left Nat.one_le_two_pow _
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- The final cardinality dyadic-bin factor is at most the cardinality plus
one.  This also covers cardinality zero. -/
theorem continuumCriticalSingleDyadicBinFactor_one_natCast_le_add_one
    (n : Nat) :
    continuumCriticalSingleDyadicBinFactor 1 (n : Real) <= n + 1 := by
  have hbucketOne : dyadicCeilBucket 1 = 0 := by
    norm_num [dyadicCeilBucket, Real.logb]
  have hbucketN :
      dyadicCeilBucket (n : Real) = (Nat.clog 2 n : Int) := by
    calc
      ⌈Real.logb 2 (n : Real)⌉ = Int.clog 2 (n : Real) :=
        Real.ceil_logb_natCast (by exact_mod_cast Nat.zero_le n)
      _ = (Nat.clog 2 n : Int) := Int.clog_natCast 2 n
  have hclog : Nat.clog 2 n <= n := by
    exact Nat.clog_le_of_le_pow (self_le_two_pow n)
  unfold continuumCriticalSingleDyadicBinFactor
  rw [hbucketOne, hbucketN]
  norm_num
  exact hclog

/-- The radius-dependent uniform norm/tangency bin slack is at most a fixed
constant times `radius ^ (-1)`. -/
theorem pyzCriticalBinUniformSlack_real_le_div
    (radius : NNReal) (hradius : 0 < radius)
    (hradiusSmall : radius <= (1 / 100 : NNReal)) :
    (pyzCriticalBinUniformSlack (radius : Real) : Real) <=
      2306 / (radius : Real) := by
  have hradiusReal : 0 < (radius : Real) := NNReal.coe_pos.mpr hradius
  have hradius1152 : (radius : Real) <= 1152 := by
    have hradiusRealSmall : (radius : Real) <= (1 : Real) / 100 := by
      exact_mod_cast hradiusSmall
    linarith
  let upper : Int := dyadicCeilBucket 1152
  let lower : Int := dyadicCeilBucket (radius : Real)
  have hlowerUpper : lower <= upper := by
    dsimp only [lower, upper]
    exact dyadicCeilBucket_mono hradiusReal hradius1152
  have hwindowNonneg : 0 <= upper + 1 - lower := by omega
  have htoNatCast :
      (((upper + 1 - lower).toNat : Nat) : Real) =
        ((upper + 1 - lower : Int) : Real) := by
    exact_mod_cast (Int.toNat_of_nonneg hwindowNonneg)
  have hupperCeil :
      (upper : Real) < Real.logb 2 1152 + 1 := by
    exact Int.ceil_lt_add_one (Real.logb 2 1152)
  have hlowerCeil :
      Real.logb 2 (radius : Real) <= (lower : Real) := by
    exact Int.le_ceil (Real.logb 2 (radius : Real))
  have hwindow :
      (pyzCriticalBinUniformSlack (radius : Real) : Real) <=
        Real.logb 2 1152 - Real.logb 2 (radius : Real) + 2 := by
    unfold pyzCriticalBinUniformSlack
    unfold continuumCriticalSingleDyadicBinFactor
    change (((upper + 1 - lower).toNat : Nat) : Real) <= _
    rw [htoNatCast]
    push_cast
    linarith
  let x : Real := 1152 / (radius : Real)
  have hxPos : 0 < x := div_pos (by norm_num) hradiusReal
  have hlogDiff :
      Real.logb 2 1152 - Real.logb 2 (radius : Real) =
        Real.log x / Real.log 2 := by
    unfold Real.logb
    dsimp only [x]
    rw [Real.log_div (by norm_num) hradiusReal.ne']
    ring
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 : Real) / 2 <= Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have htwoLog : (1 : Real) <= 2 * Real.log 2 := by linarith
  have hlogX : Real.log x <= x := by
    exact (Real.log_le_sub_one_of_pos hxPos).trans (by linarith)
  have hxLe : x <= 2 * x * Real.log 2 := by
    calc
      x = x * 1 := by ring
      _ <= x * (2 * Real.log 2) :=
        mul_le_mul_of_nonneg_left htwoLog hxPos.le
      _ = 2 * x * Real.log 2 := by ring
  have hlogDiv : Real.log x / Real.log 2 <= 2 * x := by
    apply (div_le_iff₀ hlogTwoPos).2
    exact hlogX.trans hxLe
  have hradiusOne : (radius : Real) <= 1 := by
    have hsmall : (radius : Real) <= (1 : Real) / 100 := by
      exact_mod_cast hradiusSmall
    linarith
  have htwo : (2 : Real) <= 2 / (radius : Real) := by
    apply (le_div_iff₀ hradiusReal).2
    nlinarith
  calc
    (pyzCriticalBinUniformSlack (radius : Real) : Real) <=
        Real.logb 2 1152 - Real.logb 2 (radius : Real) + 2 := hwindow
    _ = Real.log x / Real.log 2 + 2 := by rw [hlogDiff]
    _ <= 2 * x + 2 := by gcongr
    _ <= 2 * (1152 / (radius : Real)) +
        2 / (radius : Real) := by
      dsimp only [x]
      gcongr
    _ = 2306 / (radius : Real) := by ring

theorem pyzCriticalBinUniformSlack_coe_le_rpow_neg_one
    (radius : NNReal) (hradius : 0 < radius)
    (hradiusSmall : radius <= (1 / 100 : NNReal)) :
    (pyzCriticalBinUniformSlack (radius : Real) : ENNReal) <=
      2306 * (radius : ENNReal) ^ (-1 : Real) := by
  have hreal := pyzCriticalBinUniformSlack_real_le_div
    radius hradius hradiusSmall
  have hrpow :
      (radius : Real) ^ (-1 : Real) = ((radius : Real))⁻¹ := by
    rw [show (-1 : Real) = ((-1 : Int) : Real) by norm_num,
      Real.rpow_intCast]
    norm_num
  have hreal' :
      (pyzCriticalBinUniformSlack (radius : Real) : Real) <=
        2306 * (radius : Real) ^ (-1 : Real) := by
    rw [hrpow]
    simpa [div_eq_mul_inv] using hreal
  have hnn :
      (pyzCriticalBinUniformSlack (radius : Real) : NNReal) <=
        2306 * radius ^ (-1 : Real) := by
    rw [← NNReal.coe_le_coe]
    simpa only [NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_mul,
      NNReal.coe_rpow] using hreal'
  rw [← ENNReal.coe_rpow_of_ne_zero hradius.ne' (-1 : Real)]
  exact_mod_cast hnn

/-- The fourth-power loss after global packing. -/
def nativeHighDyadicPairPackingConstant : ENNReal :=
  10368 * nativeHighAmbientPackingConstant ^ 4

theorem two_mul_card_fourth_coe_le_ambientPacking_rpow
    {radius : NNReal} (hradius : 0 < radius)
    {n : Nat}
    (hn : (n : ENNReal) <= nativeHighAmbientPackingConstant *
      (radius : ENNReal) ^ (-5 : Real)) :
    (((2 * n) ^ 4 : Nat) : ENNReal) <=
      16 * nativeHighAmbientPackingConstant ^ 4 *
        (radius : ENNReal) ^ (-20 : Real) := by
  have hpow :
      (n : ENNReal) ^ 4 <=
        (nativeHighAmbientPackingConstant *
          (radius : ENNReal) ^ (-5 : Real)) ^ 4 := by
    gcongr
  have hradius0 : (radius : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hradius.ne'
  have hradiusTop : (radius : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (((2 * n) ^ 4 : Nat) : ENNReal) =
        16 * (n : ENNReal) ^ 4 := by
      push_cast
      ring
    _ <= 16 * (nativeHighAmbientPackingConstant *
          (radius : ENNReal) ^ (-5 : Real)) ^ 4 := by gcongr
    _ = 16 * nativeHighAmbientPackingConstant ^ 4 *
        ((radius : ENNReal) ^ (-5 : Real)) ^ 4 := by
      rw [mul_pow]
      ring
    _ = 16 * nativeHighAmbientPackingConstant ^ 4 *
        (radius : ENNReal) ^ (-20 : Real) := by
      rw [← ENNReal.rpow_natCast
        ((radius : ENNReal) ^ (-5 : Real)) 4]
      rw [← ENNReal.rpow_mul]
      norm_num

theorem nativeHighDyadicPairLossMax_le_extremalPacking_rpow
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (H : NativeHighGeometry D)
    {Y : Shading D.S.family.bodyFamily} {parallelLoss : Nat}
    {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily D.S.family Y D.ambient parallelLoss
      epsilon sigma)
    (hradiusSmall : radius <= (1 / 100 : NNReal)) :
    nativeHighDyadicPairLossMax D H <=
      nativeHighDyadicPairPackingConstant *
        (radius : ENNReal) ^ (-20 : Real) := by
  have hambient :
      (D.physical.ambient.card : ENNReal) <=
        nativeHighAmbientPackingConstant *
          (radius : ENNReal) ^ (-5 : Real) := by
    change (D.ambient.card : ENNReal) <=
      nativeHighAmbientPackingConstant *
        (radius : ENNReal) ^ (-5 : Real)
    exact extremalAmbient_card_coe_le_nativeHighAmbientPacking_rpow
      D.S D.ambient G hradiusSmall
  have hfourth := two_mul_card_fourth_coe_le_ambientPacking_rpow
    G.delta_pos hambient
  calc
    nativeHighDyadicPairLossMax D H <=
        648 * (((2 * D.physical.ambient.card) ^ 4 : Nat) : ENNReal) :=
      nativeHighDyadicPairLossMax_le_ambientCardFourth D H
    _ <= 648 * (16 * nativeHighAmbientPackingConstant ^ 4 *
        (radius : ENNReal) ^ (-20 : Real)) := by gcongr
    _ = nativeHighDyadicPairPackingConstant *
        (radius : ENNReal) ^ (-20 : Real) := by
      unfold nativeHighDyadicPairPackingConstant
      ring

/-- The last cardinality bin is also uniform after global ambient packing. -/
def nativeHighFinalCardBinPackingConstant : ENNReal :=
  nativeHighAmbientPackingConstant + 1

theorem finalCardBinFactor_le_extremalPacking_rpow
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    {Y : Shading D.S.family.bodyFamily} {parallelLoss : Nat}
    {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily D.S.family Y D.ambient parallelLoss
      epsilon sigma)
    (hradiusSmall : radius <= (1 / 100 : NNReal)) :
    (continuumCriticalSingleDyadicBinFactor 1
        (D.physical.ambient.card : Real) : ENNReal) <=
      nativeHighFinalCardBinPackingConstant *
        (radius : ENNReal) ^ (-5 : Real) := by
  have hbinNat :=
    continuumCriticalSingleDyadicBinFactor_one_natCast_le_add_one
      D.physical.ambient.card
  have hbin :
      (continuumCriticalSingleDyadicBinFactor 1
          (D.physical.ambient.card : Real) : ENNReal) <=
        (D.physical.ambient.card : ENNReal) + 1 := by
    exact_mod_cast hbinNat
  have hambient :
      (D.physical.ambient.card : ENNReal) <=
        nativeHighAmbientPackingConstant *
          (radius : ENNReal) ^ (-5 : Real) := by
    change (D.ambient.card : ENNReal) <=
      nativeHighAmbientPackingConstant *
        (radius : ENNReal) ^ (-5 : Real)
    exact extremalAmbient_card_coe_le_nativeHighAmbientPacking_rpow
      D.S D.ambient G hradiusSmall
  have hradiusOne : (radius : ENNReal) <= 1 := by
    exact_mod_cast (hradiusSmall.trans (by
      exact_mod_cast (show (1 : Real) / 100 <= 1 by norm_num)))
  have hpowerOne : 1 <= (radius : ENNReal) ^ (-5 : Real) := by
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr G.delta_pos) hradiusOne (by norm_num)
  calc
    (continuumCriticalSingleDyadicBinFactor 1
        (D.physical.ambient.card : Real) : ENNReal) <=
        (D.physical.ambient.card : ENNReal) + 1 := hbin
    _ <= nativeHighAmbientPackingConstant *
          (radius : ENNReal) ^ (-5 : Real) + 1 := by gcongr
    _ <= nativeHighAmbientPackingConstant *
          (radius : ENNReal) ^ (-5 : Real) +
        (radius : ENNReal) ^ (-5 : Real) := by gcongr
    _ = nativeHighFinalCardBinPackingConstant *
        (radius : ENNReal) ^ (-5 : Real) := by
      unfold nativeHighFinalCardBinPackingConstant
      ring

/-- Final fixed constant for the entire native-high scalar seam. -/
def nativeHighUniformCoefficientConstant : ENNReal :=
  2306 * nativeHighFinalCardBinPackingConstant *
    nativeHighDyadicPairPackingConstant

/-- Genuine producer geometry gives a datum-uniform polynomial upper bound
for the entire native-high coefficient. -/
theorem postNormBinLoss_mul_nativeHighDyadicPairLossMax_le_uniform_rpow
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (H : NativeHighGeometry D)
    {Y : Shading D.S.family.bodyFamily} {parallelLoss : Nat}
    {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily D.S.family Y D.ambient parallelLoss
      epsilon sigma)
    (hradiusSmall : radius <= (1 / 100 : NNReal))
    (hglobalScaleUpper : D.globalScale <= 32) :
    actualAllCenterPostNormBinLoss radius D.globalScale
        D.physical.ambient.card * nativeHighDyadicPairLossMax D H <=
      nativeHighUniformCoefficientConstant *
        (radius : ENNReal) ^ (-26 : Real) := by
  have hpost := actualAllCenterPostNormBinLoss_le_of_globalScale_le_32
    D hglobalScaleUpper
  have hslack := pyzCriticalBinUniformSlack_coe_le_rpow_neg_one
    radius G.delta_pos hradiusSmall
  have hfinal := finalCardBinFactor_le_extremalPacking_rpow
    D G hradiusSmall
  have hpair := nativeHighDyadicPairLossMax_le_extremalPacking_rpow
    D H G hradiusSmall
  have hradius0 : (radius : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr G.delta_pos.ne'
  have hradiusTop : (radius : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    actualAllCenterPostNormBinLoss radius D.globalScale
        D.physical.ambient.card * nativeHighDyadicPairLossMax D H <=
      ((pyzCriticalBinUniformSlack (radius : Real) : ENNReal) *
        (continuumCriticalSingleDyadicBinFactor 1
          (D.physical.ambient.card : Real) : ENNReal)) *
        nativeHighDyadicPairLossMax D H := by gcongr
    _ <= ((2306 * (radius : ENNReal) ^ (-1 : Real)) *
        (nativeHighFinalCardBinPackingConstant *
          (radius : ENNReal) ^ (-5 : Real))) *
        (nativeHighDyadicPairPackingConstant *
          (radius : ENNReal) ^ (-20 : Real)) := by gcongr
    _ = nativeHighUniformCoefficientConstant *
        (((radius : ENNReal) ^ (-1 : Real) *
          (radius : ENNReal) ^ (-5 : Real)) *
          (radius : ENNReal) ^ (-20 : Real)) := by
      unfold nativeHighUniformCoefficientConstant
      ring
    _ = nativeHighUniformCoefficientConstant *
        (radius : ENNReal) ^ (-26 : Real) := by
      rw [← ENNReal.rpow_add (-1 : Real) (-5 : Real) hradius0 hradiusTop]
      norm_num
      rw [← ENNReal.rpow_add (-6 : Real) (-20 : Real) hradius0 hradiusTop]
      norm_num

#print axioms continuumCriticalSingleDyadicBinFactor_one_natCast_le_add_one
#print axioms pyzCriticalBinUniformSlack_real_le_div
#print axioms pyzCriticalBinUniformSlack_coe_le_rpow_neg_one
#print axioms nativeHighDyadicPairPackingConstant
#print axioms two_mul_card_fourth_coe_le_ambientPacking_rpow
#print axioms nativeHighDyadicPairLossMax_le_extremalPacking_rpow
#print axioms nativeHighFinalCardBinPackingConstant
#print axioms finalCardBinFactor_le_extremalPacking_rpow
#print axioms nativeHighUniformCoefficientConstant
#print axioms postNormBinLoss_mul_nativeHighDyadicPairLossMax_le_uniform_rpow

end
end Family8Family7NativeHighUniformCoefficientV1
