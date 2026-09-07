import Family8Grounding.Family8StickyFiberContractedJohnProxyKatzTaoV2
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8ContractedJohnAffineJacobianLowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8TubeJohnContractedLipschitzV1
open Family8TubeJohnOuterEllipsoidUnitBallV3
open Family8TubeJohnUnitRescalingV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# A fixed lower bound for the contracted John Jacobian

The genuine inner John ellipsoid gives a radius-`1/24` ball in the
contracted image.  The parent tube has volume at most `12*rho^2` when
`rho <= 1`.  Thus the inverse Jacobian cancels the apparent inverse-square
loss in the proxy Katz--Tao constant, without inspecting a chosen witness's
semiaxes.
-/

theorem closedBall_third_subset_image_innerAxisEllipsoid
    {rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) :
    Metric.closedBall (0 : Space) (1 / 3 : Real) ⊆
      axisEllipsoidNormalizationAffineEquiv
          w.center w.frame w.radius
          (fun i =>
            Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube
              P hrho w i) ''
        axisEllipsoid w.center w.frame w.radius 1 := by
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  have hySq : ‖y‖ ^ 2 <= (1 / 3 : Real) ^ 2 := by
    nlinarith [norm_nonneg y]
  let z : Fin 3 -> Real := fun i => 3 * ⟪w.frame i, y⟫_Real
  have hparseval := w.frame.sum_sq_inner_right y
  have hz : ∑ i, (z i) ^ 2 <= (1 : Real) ^ 2 := by
    rw [Fin.sum_univ_three] at hparseval ⊢
    dsimp only [z]
    norm_num at hparseval ⊢
    nlinarith
  let R := axisEllipsoidNormalizationAffineEquiv
    w.center w.frame w.radius
      (fun i =>
        Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube
          P hrho w i)
  refine ⟨R.symm y, ?_, R.apply_symm_apply y⟩
  refine ⟨z, hz, ?_⟩
  dsimp only [R]
  rw [axisEllipsoidNormalizationAffineEquiv_symm_apply]
  congr 2
  funext i
  dsimp only [z]
  ring_nf

theorem closedBall_twentyFourth_subset_image_contractedTubeJohn
    {rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) :
    Metric.closedBall (0 : Space) (1 / 24 : Real) ⊆
      contractedTubeJohnAffineEquiv P hrho w '' P.carrier := by
  intro y hy
  have hyNorm : ‖y‖ <= (1 / 24 : Real) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  let z : Space := (8 : Real) • y
  have hzNorm : ‖z‖ <= (1 / 3 : Real) := by
    dsimp only [z]
    rw [norm_smul, Real.norm_ofNat]
    nlinarith
  have hzBall : z ∈ Metric.closedBall (0 : Space) (1 / 3 : Real) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzNorm
  obtain ⟨x, hxInner, hxImage⟩ :=
    closedBall_third_subset_image_innerAxisEllipsoid P hrho w hzBall
  refine ⟨x, w.inner hxInner, ?_⟩
  rw [contractedTubeJohnAffineEquiv_apply, hxImage]
  dsimp only [z]
  module

theorem Tube.volume_le_twelve_mul_sq_of_le_one
    {rho : NNReal} (P : Tube rho) (hrhoOne : rho <= 1) :
    volume P.carrier <= 12 * (rho : ENNReal) ^ 2 := by
  obtain ⟨frame, hframe⟩ := P.exists_alignedFrame
  have hbox : volume P.carrier <=
      volume (P.alignedFrameBox frame).carrier :=
    measure_mono (P.carrier_subset_alignedFrameBox frame hframe)
  have hrhoE : (rho : ENNReal) <= 1 := by
    exact_mod_cast hrhoOne
  calc
    volume P.carrier <= volume (P.alignedFrameBox frame).carrier := hbox
    _ = 4 * (rho : ENNReal) ^ 2 * (1 + 2 * (rho : ENNReal)) := by
      rw [FrameBox.volume_carrier]
      simp [Tube.alignedFrameBox, Tube.frameBoxSides, Fin.prod_univ_three]
      ring
    _ <= 4 * (rho : ENNReal) ^ 2 * 3 := by
      gcongr
      calc
        1 + 2 * (rho : ENNReal) <= 1 + 2 * 1 := by gcongr
        _ = 3 := by norm_num
    _ = 12 * (rho : ENNReal) ^ 2 := by ring

theorem four_mul_twentyFourth_pow_three_le_volume_closedBall :
    4 * (1 / 24 : ENNReal) ^ 3 <=
      volume (Metric.closedBall (0 : Space) (1 / 24 : Real)) := by
  rw [EuclideanSpace.volume_closedBall_fin_three]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 24)]
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  have hreal : (4 : Real) <= Real.pi * 4 / 3 := by
    nlinarith [Real.pi_gt_three]
  have hcoeff := ENNReal.ofReal_le_ofReal hreal
  calc
    4 * (1 / 24 : ENNReal) ^ 3 =
        (1 / 24 : ENNReal) ^ 3 * 4 := by ring
    _ <= (1 / 24 : ENNReal) ^ 3 *
        ENNReal.ofReal (Real.pi * 4 / 3) := by
      gcongr
      simpa using hcoeff

theorem one_le_41472_mul_affineJacobian_mul_rho_sq
    {rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (w : JohnAxisWitness P.body) :
    1 <= 41472 * affineJacobian
        (contractedTubeJohnAffineEquiv P hrho w) * (rho : ENNReal) ^ 2 := by
  let e := contractedTubeJohnAffineEquiv P hrho w
  have hvolume :
      4 * (1 / 24 : ENNReal) ^ 3 <=
        affineJacobian e * (12 * (rho : ENNReal) ^ 2) := by
    calc
      4 * (1 / 24 : ENNReal) ^ 3 <=
          volume (Metric.closedBall (0 : Space) (1 / 24 : Real)) :=
        four_mul_twentyFourth_pow_three_le_volume_closedBall
      _ <= volume (e '' P.carrier) :=
        measure_mono
          (closedBall_twentyFourth_subset_image_contractedTubeJohn P hrho w)
      _ = affineJacobian e * volume P.carrier :=
        volume_image_affineEquiv e P.carrier
      _ <= affineJacobian e * (12 * (rho : ENNReal) ^ 2) := by
        gcongr
        exact Family8ContractedJohnAffineJacobianLowerV3.Tube.volume_le_twelve_mul_sq_of_le_one
          P hrhoOne
  have hnumeric :
      3456 * (4 * (1 / 24 : ENNReal) ^ 3) = 1 := by
    have hleftTop :
        3456 * (4 * (1 / 24 : ENNReal) ^ 3) ≠ ∞ := by
      apply ENNReal.mul_ne_top (by norm_num)
      apply ENNReal.mul_ne_top (by norm_num)
      exact ENNReal.pow_ne_top
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
    apply (ENNReal.toReal_eq_toReal_iff' hleftTop (by norm_num)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div]
  calc
    (1 : ENNReal) = 3456 * (4 * (1 / 24 : ENNReal) ^ 3) := hnumeric.symm
    _ <= 3456 * (affineJacobian e * (12 * (rho : ENNReal) ^ 2)) := by
      gcongr
    _ = 41472 * affineJacobian e * (rho : ENNReal) ^ 2 := by ring

theorem contractedJohnProxyVolumeRatio_eq
    {delta rho : NNReal} (hdelta : 0 < delta) (hrho : 0 < rho) :
    contractedJohnProxyVolumeRatio delta rho =
      9 / (4 * (rho : ENNReal) ^ 2) := by
  have hleftTop : contractedJohnProxyVolumeRatio delta rho ≠ ∞ := by
    unfold contractedJohnProxyVolumeRatio
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact ENNReal.div_ne_zero.mpr
        ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩
  have hrightTop : 9 / (4 * (rho : ENNReal) ^ 2) ≠ ∞ := by
    apply ENNReal.div_ne_top (by norm_num)
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hrho.ne'))
  apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).mp
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdelta
  have hrhoReal : 0 < (rho : Real) := NNReal.coe_pos.mpr hrho
  norm_num [contractedJohnProxyVolumeRatio, contractedJohnProxyRadius,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.coe_div]
  field_simp
  ring

theorem contractedJohnProxyVolumeRatio_div_affineJacobian_le
    {delta rho : NNReal} (P : Tube rho) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (w : JohnAxisWitness P.body) :
    contractedJohnProxyVolumeRatio delta rho /
        affineJacobian (contractedTubeJohnAffineEquiv P hrho w) <= 93312 := by
  let J := affineJacobian (contractedTubeJohnAffineEquiv P hrho w)
  have hJ0 : J ≠ 0 :=
    (affineJacobian_pos (contractedTubeJohnAffineEquiv P hrho w)).ne'
  have hJTop : J ≠ ∞ := affineJacobian_ne_top _
  have hrhoSq0 : (rho : ENNReal) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hrho.ne')
  have hden0 : 4 * (rho : ENNReal) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) hrhoSq0
  have hdenTop : 4 * (rho : ENNReal) ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  rw [contractedJohnProxyVolumeRatio_eq hdelta hrho]
  apply (ENNReal.div_le_iff hJ0 hJTop).2
  apply (ENNReal.div_le_iff hden0 hdenTop).2
  have hbase := one_le_41472_mul_affineJacobian_mul_rho_sq
    P hrho hrhoOne w
  calc
    (9 : ENNReal) = 9 * 1 := by norm_num
    _ <= 9 * (41472 * J * (rho : ENNReal) ^ 2) := by gcongr
    _ = 93312 * J * (4 * (rho : ENNReal) ^ 2) := by ring

theorem stickyFiberContractedJohnProxyKatzTaoConstant_le_fixed
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) (C : ENNReal) :
    stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne k C <= 93312 * C := by
  let ratio := contractedJohnProxyVolumeRatio delta rho
  let J := affineJacobian
    (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
  have hratio : ratio / J <= 93312 := by
    exact contractedJohnProxyVolumeRatio_div_affineJacobian_le
      (S.coarse.tubes k.1) hdelta hrho hrhoOne
      (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
        S hrho hrhoOne k)
  unfold stickyFiberContractedJohnProxyKatzTaoConstant
  change ratio * C / J <= 93312 * C
  calc
    ratio * C / J = (ratio / J) * C := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ <= 93312 * C := by gcongr

#print axioms closedBall_third_subset_image_innerAxisEllipsoid
#print axioms closedBall_twentyFourth_subset_image_contractedTubeJohn
#print axioms Tube.volume_le_twelve_mul_sq_of_le_one
#print axioms four_mul_twentyFourth_pow_three_le_volume_closedBall
#print axioms one_le_41472_mul_affineJacobian_mul_rho_sq
#print axioms contractedJohnProxyVolumeRatio_eq
#print axioms contractedJohnProxyVolumeRatio_div_affineJacobian_le
#print axioms stickyFiberContractedJohnProxyKatzTaoConstant_le_fixed

end
end Family8ContractedJohnAffineJacobianLowerV3
