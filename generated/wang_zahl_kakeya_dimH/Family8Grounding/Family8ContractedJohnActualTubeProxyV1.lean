import Family8Grounding.Family8TubeJohnContractedLipschitzV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ContractedJohnActualTubeProxyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8TubeJohnUnitRescalingV2
open Family8TubeJohnOuterEllipsoidUnitBallV3
open Family8TubeJohnWitnessPositiveRadiiV4
open Family8TubeJohnContractedLipschitzV1

noncomputable section

/-!
# A genuine tube proxy for one contracted John image

An affine image of a Euclidean tube is generally not a Euclidean tube.  For
the actual Frostman interface we instead extend the image of its unit axis
to a genuine unit segment and thicken that segment by the proved Lipschitz
radius `3*delta/(8*rho)`.  All definitions below are canonical and every
containment is proved from the real tube and John witness.
-/

/-! ## Unit extension of an affine image axis -/

/-- Difference of the transformed endpoints of a tube axis. -/
def affineImageAxisVector {delta : NNReal} (e : Space ≃ᵃ[Real] Space)
    (T : Tube delta) : Space :=
  e T.axis.endpoint - e T.axis.base

theorem affineImageAxisVector_ne_zero
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    affineImageAxisVector e T ≠ 0 := by
  intro hzero
  have himage : e T.axis.endpoint = e T.axis.base := by
    exact sub_eq_zero.mp hzero
  have hsource : T.axis.endpoint = T.axis.base := e.injective himage
  have hdist := T.axis.dist_base_endpoint
  rw [hsource, dist_self] at hdist
  norm_num at hdist

/-- Unit direction parallel to the transformed source axis. -/
def affineImageAxisDirection {delta : NNReal}
    (e : Space ≃ᵃ[Real] Space) (T : Tube delta) : Space :=
  ‖affineImageAxisVector e T‖⁻¹ • affineImageAxisVector e T

@[simp]
theorem norm_affineImageAxisDirection
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    ‖affineImageAxisDirection e T‖ = 1 := by
  have hv : affineImageAxisVector e T ≠ 0 :=
    affineImageAxisVector_ne_zero e T
  have hvpos : 0 < ‖affineImageAxisVector e T‖ := norm_pos_iff.mpr hv
  rw [affineImageAxisDirection, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hvpos), inv_mul_cancel₀ hvpos.ne']

/-- Midpoint of the two transformed endpoints. -/
def affineImageAxisCenter {delta : NNReal}
    (e : Space ≃ᵃ[Real] Space) (T : Tube delta) : Space :=
  (1 / 2 : Real) • (e T.axis.base + e T.axis.endpoint)

/-- The genuine unit segment centered at the transformed axis midpoint and
parallel to the transformed axis. -/
def affineImageUnitExtensionAxis {delta : NNReal}
    (e : Space ≃ᵃ[Real] Space) (T : Tube delta) : UnitSegment where
  base := affineImageAxisCenter e T -
    (1 / 2 : Real) • affineImageAxisDirection e T
  direction := affineImageAxisDirection e T
  norm_direction := norm_affineImageAxisDirection e T

@[simp]
theorem affineImageUnitExtensionAxis_direction
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    (affineImageUnitExtensionAxis e T).direction =
      affineImageAxisDirection e T :=
  rfl

@[simp]
theorem affineImageUnitExtensionAxis_base
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    (affineImageUnitExtensionAxis e T).base =
      affineImageAxisCenter e T -
        (1 / 2 : Real) • affineImageAxisDirection e T :=
  rfl

/-- The endpoint difference is the linear image of the source direction. -/
theorem affineImageAxisVector_eq_linear
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    affineImageAxisVector e T = e.linear T.axis.direction := by
  unfold affineImageAxisVector UnitSegment.endpoint
  rw [show T.axis.base + T.axis.direction =
    T.axis.direction +ᵥ T.axis.base by
      simp only [vadd_eq_add]
      abel]
  rw [e.map_vadd]
  simp

/-- If the transformed source axis has length at most one, its literal image
lies in the centered unit extension. -/
theorem image_axis_carrier_subset_affineImageUnitExtensionAxis
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta)
    (hlength : ‖affineImageAxisVector e T‖ <= 1) :
    e '' T.axis.carrier ⊆ (affineImageUnitExtensionAxis e T).carrier := by
  rintro _ ⟨x, hx, rfl⟩
  rw [T.axis.carrier_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  let v := affineImageAxisVector e T
  let ell : Real := ‖v‖
  let d := affineImageAxisDirection e T
  let u : Real := 1 / 2 + (t - 1 / 2) * ell
  have hell0 : 0 <= ell := norm_nonneg _
  have hell1 : ell <= 1 := hlength
  have hu : u ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> dsimp only [u] <;> nlinarith [ht.1, ht.2]
  have hvne : v ≠ 0 := affineImageAxisVector_ne_zero e T
  have hellpos : 0 < ell := norm_pos_iff.mpr hvne
  have helld : ell • d = v := by
    dsimp only [d, ell, affineImageAxisDirection]
    rw [smul_smul, mul_inv_cancel₀ hellpos.ne', one_smul]
  have hvlinear : v = e.linear T.axis.direction := by
    exact affineImageAxisVector_eq_linear e T
  have hmap :
      e (T.axis.base + t • T.axis.direction) =
        e T.axis.base + t • v := by
    rw [show T.axis.base + t • T.axis.direction =
      (t • T.axis.direction) +ᵥ T.axis.base by
        simp only [vadd_eq_add]
        abel]
    rw [e.map_vadd, map_smul, ← hvlinear]
    simp only [vadd_eq_add]
    abel
  have hendpoint : e T.axis.endpoint = e T.axis.base + v := by
    dsimp only [v, affineImageAxisVector]
    abel
  rw [hmap]
  rw [UnitSegment.carrier_eq_image]
  refine ⟨u, hu, ?_⟩
  dsimp only [affineImageUnitExtensionAxis,
    affineImageUnitExtensionAxis_base,
    affineImageUnitExtensionAxis_direction,
    affineImageAxisCenter]
  dsimp only [u, d] at helld ⊢
  rw [hendpoint]
  rw [← helld]
  module

/-! ## The contracted John specialization -/

/-- The actual proxy radius forced by the contracted John Lipschitz bound. -/
def contractedJohnProxyRadius (delta rho : NNReal) : NNReal :=
  (3 * delta) / (8 * rho)

theorem contractedJohnProxyRadius_pos
    {delta rho : NNReal} (hdelta : 0 < delta) (hrho : 0 < rho) :
    0 < contractedJohnProxyRadius delta rho := by
  exact div_pos (mul_pos (by norm_num) hdelta) (mul_pos (by norm_num) hrho)

/-- The contracted John map sends its real parent tube into the radius-`1/8`
ball. -/
theorem image_parent_carrier_subset_closedBall_eighth
    {rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) :
    contractedTubeJohnAffineEquiv P hrho w '' P.carrier ⊆
      Metric.closedBall (0 : Space) (1 / 8 : Real) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right,
    contractedTubeJohnAffineEquiv_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : Real) < 1 / 8)]
  have hxOuter : x ∈ axisEllipsoid w.center w.frame w.radius 3 := by
    exact w.outer (by simpa only [Tube.coe_body] using hx)
  have hxBall :
      axisEllipsoidNormalizationAffineEquiv w.center w.frame w.radius
          (fun i =>
            Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube
              P hrho w i) x ∈ Metric.closedBall (0 : Space) 1 := by
    rw [← image_axisEllipsoid_three_eq_closedBall
      w.center w.frame w.radius
      (fun i =>
        Family8TubeJohnWitnessPositiveRadiiV4.JohnAxisWitness.radius_pos_of_tube
          P hrho w i)]
    exact ⟨x, hxOuter, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hxBall
  nlinarith

/-- Containment in the real parent makes the contracted image axis shorter
than `1/4`, so the unit extension theorem applies without a premise. -/
theorem norm_affineImageAxisVector_contracted_le_quarter
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta)
    (hTP : T.carrier ⊆ P.carrier) :
    ‖affineImageAxisVector (contractedTubeJohnAffineEquiv P hrho w) T‖ <=
      (1 / 4 : Real) := by
  let e := contractedTubeJohnAffineEquiv P hrho w
  have hbaseParent : T.axis.base ∈ P.carrier :=
    hTP (T.axis_subset_carrier T.axis.base_mem_carrier)
  have hendParent : T.axis.endpoint ∈ P.carrier :=
    hTP (T.axis_subset_carrier T.axis.endpoint_mem_carrier)
  have hbase := image_parent_carrier_subset_closedBall_eighth
    P hrho w ⟨T.axis.base, hbaseParent, rfl⟩
  have hend := image_parent_carrier_subset_closedBall_eighth
    P hrho w ⟨T.axis.endpoint, hendParent, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hbase hend
  change ‖e T.axis.endpoint - e T.axis.base‖ <= (1 / 4 : Real)
  calc
    ‖e T.axis.endpoint - e T.axis.base‖ <=
        ‖e T.axis.endpoint‖ + ‖e T.axis.base‖ := norm_sub_le _ _
    _ <= (1 / 8 : Real) + (1 / 8 : Real) := by
      exact add_le_add (by simpa only [e] using hend)
        (by simpa only [e] using hbase)
    _ = (1 / 4 : Real) := by norm_num

/-- The genuine project tube proxy around the centered image-axis
extension. -/
def contractedJohnProxyTube
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) :
    Tube (contractedJohnProxyRadius delta rho) where
  axis := affineImageUnitExtensionAxis
    (contractedTubeJohnAffineEquiv P hrho w) T

@[simp]
theorem contractedJohnProxyTube_axis
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) :
    (contractedJohnProxyTube P hrho w T).axis =
      affineImageUnitExtensionAxis
        (contractedTubeJohnAffineEquiv P hrho w) T :=
  rfl

/-- The contracted affine image of the real child tube is contained in its
genuine project-tube proxy. -/
theorem image_child_carrier_subset_contractedJohnProxyTube
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta)
    (hTP : T.carrier ⊆ P.carrier) :
    contractedTubeJohnAffineEquiv P hrho w '' T.carrier ⊆
      (contractedJohnProxyTube P hrho w T).carrier := by
  let e := contractedTubeJohnAffineEquiv P hrho w
  have haxisLength : ‖affineImageAxisVector e T‖ <= 1 :=
    (norm_affineImageAxisVector_contracted_le_quarter
      P hrho w T hTP).trans (by norm_num)
  have haxisImage : e '' T.axis.carrier ⊆
      (affineImageUnitExtensionAxis e T).carrier :=
    image_axis_carrier_subset_affineImageUnitExtensionAxis
      e T haxisLength
  rintro _ ⟨x, hx, rfl⟩
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 <= (delta : Real) by positivity)] at hx
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨a, haAxis, hxa⟩ := hx
  have haProxy : e a ∈ (affineImageUnitExtensionAxis e T).carrier :=
    haxisImage ⟨a, haAxis, rfl⟩
  have hdist : dist (e x) (e a) <=
      (contractedJohnProxyRadius delta rho : Real) := by
    calc
      dist (e x) (e a) <=
          (3 / (8 * (rho : Real))) * dist x a :=
        contractedTubeJohnAffineEquiv_dist_le P hrho w x a
      _ <= (3 / (8 * (rho : Real))) * (delta : Real) := by gcongr
      _ = (contractedJohnProxyRadius delta rho : Real) := by
        simp only [contractedJohnProxyRadius, NNReal.coe_div,
          NNReal.coe_mul, NNReal.coe_ofNat]
        field_simp
  change e x ∈ Metric.cthickening
    (contractedJohnProxyRadius delta rho : Real)
      (affineImageUnitExtensionAxis e T).carrier
  exact Metric.closedBall_subset_cthickening haProxy _ hdist

#print axioms affineImageAxisVector_ne_zero
#print axioms norm_affineImageAxisDirection
#print axioms affineImageAxisVector_eq_linear
#print axioms image_axis_carrier_subset_affineImageUnitExtensionAxis
#print axioms contractedJohnProxyRadius_pos
#print axioms image_parent_carrier_subset_closedBall_eighth
#print axioms norm_affineImageAxisVector_contracted_le_quarter
#print axioms image_child_carrier_subset_contractedJohnProxyTube

end
end Family8ContractedJohnActualTubeProxyV1
