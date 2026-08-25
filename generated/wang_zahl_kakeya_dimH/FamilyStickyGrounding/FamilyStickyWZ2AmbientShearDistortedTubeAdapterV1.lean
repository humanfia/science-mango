import FamilyStickyGrounding.FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
import FamilyStickyGrounding.JohnActualDimThreeCertificate2
import Submission.Kakeya.ConvexFactoring.CertifiedInducedThickeningLower

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Set
open scoped NNReal

namespace FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2AmbientCinematicTranslationVolumeV1

noncomputable section

/-!
# Quantitative distorted-tube geometry for the ambient WZ2 shear

The WZ2 ambient parameter translation is an affine shear

  `(x,y,z) ↦ (x+a₀, y+b₀+d₀z, z)`.

Its inverse is Lipschitz with the safe explicit constant `1 + |d₀|`.
Consequently the affine image of a radius-`delta` tube contains a closed
ball of radius `delta / (1 + |d₀|)` around every transformed axis point.

This produces quantitative John-box side bounds directly from literal
containment of the affine tube image.  The transformed unit axis is also
retained with length at least `1 / (1 + |d₀|)`, yielding a corresponding
long-side bound.  No geometric conclusion is postulated.
-/

/-- Safe Lipschitz constant for both the shear and its inverse. -/
def inverseShearLipschitzConstant (d0 : Real) : NNReal :=
  ⟨1 + |d0|, by positivity⟩

@[simp]
theorem coe_inverseShearLipschitzConstant (d0 : Real) :
    (inverseShearLipschitzConstant d0 : Real) = 1 + |d0| :=
  rfl

theorem inverseShearLipschitzConstant_pos (d0 : Real) :
    0 < inverseShearLipschitzConstant d0 := by
  apply NNReal.coe_pos.mp
  change (0 : Real) < 1 + |d0|
  positivity

/-- Radius of the round ball that survives the ambient shear. -/
def distortedTubeRadius (delta : NNReal) (d0 : Real) : NNReal :=
  delta / inverseShearLipschitzConstant d0

/-- Guaranteed length scale of the transformed unit axis. -/
def distortedAxisLength (d0 : Real) : NNReal :=
  (inverseShearLipschitzConstant d0)⁻¹

theorem distortedTubeRadius_pos
    {delta : NNReal} (hdelta : 0 < delta) (d0 : Real) :
    0 < distortedTubeRadius delta d0 := by
  exact div_pos hdelta (inverseShearLipschitzConstant_pos d0)

theorem distortedAxisLength_pos (d0 : Real) :
    0 < distortedAxisLength d0 := by
  exact inv_pos.mpr (inverseShearLipschitzConstant_pos d0)

/-- Norm of a vector supported in the middle ambient coordinate. -/
theorem norm_point3_zero_middle_zero (y : Real) :
    ‖point3 0 y 0‖ = |y| := by
  rw [EuclideanSpace.norm_eq]
  convert Real.sqrt_sq_eq_abs y using 1
  norm_num [point3, Fin.sum_univ_succ]

/-- The ambient shear itself obeys the safe operator bound
`1 + |d₀|`; the translation parameters cancel in differences. -/
theorem norm_ambientCinematicTranslation_sub_le
    (a0 b0 d0 : Real) (p q : Space) :
    ‖ambientCinematicTranslation a0 b0 d0 p -
        ambientCinematicTranslation a0 b0 d0 q‖ <=
      (inverseShearLipschitzConstant d0 : Real) * ‖p - q‖ := by
  let e : Space := point3 0 (d0 * (p 2 - q 2)) 0
  have hdecomp :
      ambientCinematicTranslation a0 b0 d0 p -
          ambientCinematicTranslation a0 b0 d0 q =
        (p - q) + e := by
    ext i
    fin_cases i <;>
      simp [ambientCinematicTranslation, point3, e] ;
      ring
  have hcoord : |p 2 - q 2| <= ‖p - q‖ := by
    change |(p - q) 2| <= ‖p - q‖
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (p - q) (2 : Fin 3)
  rw [hdecomp]
  calc
    ‖(p - q) + e‖ <= ‖p - q‖ + ‖e‖ := norm_add_le _ _
    _ = ‖p - q‖ + |d0| * |p 2 - q 2| := by
      rw [show ‖e‖ = |d0 * (p 2 - q 2)| by
        exact norm_point3_zero_middle_zero (d0 * (p 2 - q 2))]
      rw [abs_mul]
    _ <= ‖p - q‖ + |d0| * ‖p - q‖ := by
      gcongr
    _ = (inverseShearLipschitzConstant d0 : Real) * ‖p - q‖ := by
      simp
      ring

theorem dist_ambientCinematicTranslation_le
    (a0 b0 d0 : Real) (p q : Space) :
    dist (ambientCinematicTranslation a0 b0 d0 p)
        (ambientCinematicTranslation a0 b0 d0 q) <=
      (inverseShearLipschitzConstant d0 : Real) * dist p q := by
  simpa only [dist_eq_norm] using
    norm_ambientCinematicTranslation_sub_le a0 b0 d0 p q

/-- Quantitative inverse-shear bound, expressed using the original shear
parameter rather than `-d₀`. -/
theorem dist_ambientCinematicTranslation_inverse_le
    (a0 b0 d0 : Real) (p q : Space) :
    dist (ambientCinematicTranslation (-a0) (-b0) (-d0) p)
        (ambientCinematicTranslation (-a0) (-b0) (-d0) q) <=
      (inverseShearLipschitzConstant d0 : Real) * dist p q := by
  simpa [inverseShearLipschitzConstant] using
    dist_ambientCinematicTranslation_le (-a0) (-b0) (-d0) p q

/-- Every transformed axis point is the center of a surviving round ball
inside the affine image of the tube carrier. -/
theorem closedBall_transformedAxisPoint_subset_tubeImage
    {delta : NNReal} (T : Tube delta) (a0 b0 d0 : Real)
    (p : Space) (hp : p ∈ T.axis.carrier) :
    Metric.closedBall (ambientCinematicTranslation a0 b0 d0 p)
        (distortedTubeRadius delta d0 : Real) ⊆
      ambientCinematicTranslation a0 b0 d0 '' T.carrier := by
  intro q hq
  let r := ambientCinematicTranslation (-a0) (-b0) (-d0) q
  have hqdist :
      dist q (ambientCinematicTranslation a0 b0 d0 p) <=
        (distortedTubeRadius delta d0 : Real) := by
    exact (Metric.mem_closedBall.mp hq)
  have hinverse :=
    dist_ambientCinematicTranslation_inverse_le a0 b0 d0 q
      (ambientCinematicTranslation a0 b0 d0 p)
  rw [ambientCinematicTranslation_neg_left] at hinverse
  have hLpos :
      0 < (inverseShearLipschitzConstant d0 : Real) := by
    exact_mod_cast inverseShearLipschitzConstant_pos d0
  have hrdist : dist r p <= (delta : Real) := by
    calc
      dist r p <=
          (inverseShearLipschitzConstant d0 : Real) *
            dist q (ambientCinematicTranslation a0 b0 d0 p) := hinverse
      _ <= (inverseShearLipschitzConstant d0 : Real) *
          (distortedTubeRadius delta d0 : Real) := by
        gcongr
      _ = (delta : Real) := by
        have hden : 1 + |d0| ≠ 0 := by positivity
        change (1 + |d0|) * ((delta : Real) / (1 + |d0|)) =
          (delta : Real)
        field_simp
  refine ⟨r, ?_, ?_⟩
  · apply Metric.closedBall_subset_cthickening hp
    exact Metric.mem_closedBall.mpr hrdist
  · exact ambientCinematicTranslation_neg_right a0 b0 d0 q

/-- Base-point specialization of the surviving inner-ball theorem. -/
theorem closedBall_transformedAxisBase_subset_tubeImage
    {delta : NNReal} (T : Tube delta) (a0 b0 d0 : Real) :
    Metric.closedBall
        (ambientCinematicTranslation a0 b0 d0 T.axis.base)
        (distortedTubeRadius delta d0 : Real) ⊆
      ambientCinematicTranslation a0 b0 d0 '' T.carrier :=
  closedBall_transformedAxisPoint_subset_tubeImage
    T a0 b0 d0 T.axis.base T.axis.base_mem_carrier

/-- A contained round ball forces every side of a John frame-box
certificate to have at least the ball's diameter. -/
theorem boxCertificate_side_lower_of_closedBall_subset
    {K : ConvexBody Space} {radius : NNReal} (center : Space)
    (hball : Metric.closedBall center (radius : Real) ⊆ (K : Set Space))
    {C : NNReal} {side : Fin 3 -> NNReal}
    (cert : BoxDimensionsCertificate C side K) (i : Fin 3) :
    2 * radius <= side i := by
  let p : Space := center + (radius : Real) • cert.box.frame i
  let q : Space := center - (radius : Real) • cert.box.frame i
  have hpball : p ∈ Metric.closedBall center (radius : Real) := by
    rw [Metric.mem_closedBall]
    simp [p, dist_eq_norm, norm_smul]
  have hqball : q ∈ Metric.closedBall center (radius : Real) := by
    rw [Metric.mem_closedBall]
    simp [q, norm_smul]
  have hpBox : p ∈ cert.box.carrier := cert.outer_le (hball hpball)
  have hqBox : q ∈ cert.box.carrier := cert.outer_le (hball hqball)
  have hpcoord := cert.box.centeredCoordinate_abs_le_halfSide hpBox i
  have hqcoord := cert.box.centeredCoordinate_abs_le_halfSide hqBox i
  have hside : cert.box.side i = side i := congrFun cert.side_eq i
  simp [p, q, inner_add_right, inner_sub_right, real_inner_smul_right,
    hside] at hpcoord hqcoord
  rw [abs_le] at hpcoord hqcoord
  apply NNReal.coe_le_coe.mp
  norm_num
  nlinarith [hpcoord.1, hpcoord.2, hqcoord.1, hqcoord.2]

/-- Any John certificate for a convex body containing the affine tube image
inherits the quantitative distorted-radius side lower bound. -/
theorem BoxDimensionsCertificate.side_lower_of_tubeImage_subset
    {K : ConvexBody Space} {delta : NNReal} (T : Tube delta)
    (a0 b0 d0 : Real)
    (himage :
      ambientCinematicTranslation a0 b0 d0 '' T.carrier ⊆
        (K : Set Space))
    {C : NNReal} {side : Fin 3 -> NNReal}
    (cert : BoxDimensionsCertificate C side K) (i : Fin 3) :
    2 * distortedTubeRadius delta d0 <= side i := by
  apply boxCertificate_side_lower_of_closedBall_subset
    (ambientCinematicTranslation a0 b0 d0 T.axis.base) _ cert i
  exact (closedBall_transformedAxisBase_subset_tubeImage
    T a0 b0 d0).trans himage

/-- The transformed endpoints retain at least the reciprocal inverse-shear
constant of the source unit-axis length. -/
theorem distortedAxisLength_le_dist_transformed_endpoints
    {delta : NNReal} (T : Tube delta) (a0 b0 d0 : Real) :
    (distortedAxisLength d0 : Real) <=
      dist (ambientCinematicTranslation a0 b0 d0 T.axis.base)
        (ambientCinematicTranslation a0 b0 d0 T.axis.endpoint) := by
  have hinverse :=
    dist_ambientCinematicTranslation_inverse_le a0 b0 d0
      (ambientCinematicTranslation a0 b0 d0 T.axis.base)
      (ambientCinematicTranslation a0 b0 d0 T.axis.endpoint)
  rw [ambientCinematicTranslation_neg_left,
    ambientCinematicTranslation_neg_left, T.axis.dist_base_endpoint] at hinverse
  have hLpos :
      0 < (inverseShearLipschitzConstant d0 : Real) := by
    exact_mod_cast inverseShearLipschitzConstant_pos d0
  rw [show (distortedAxisLength d0 : Real) =
      1 / (inverseShearLipschitzConstant d0 : Real) by
    simp [distortedAxisLength]]
  apply (div_le_iff₀ hLpos).2
  simpa only [one_mul, mul_comm] using hinverse

/-- The transformed axis forces one outer-box side to retain a quantitative
longitudinal scale. -/
theorem BoxDimensionsCertificate.exists_longAxis_of_tubeImage_subset
    {K : ConvexBody Space} {delta : NNReal} (T : Tube delta)
    (a0 b0 d0 : Real)
    (himage :
      ambientCinematicTranslation a0 b0 d0 '' T.carrier ⊆
        (K : Set Space))
    {C : NNReal} {side : Fin 3 -> NNReal}
    (cert : BoxDimensionsCertificate C side K) :
    ∃ j : Fin 3, distortedAxisLength d0 <= 6 * side j := by
  have hbase : ambientCinematicTranslation a0 b0 d0 T.axis.base ∈
      cert.box.carrier := by
    apply cert.outer_le
    apply himage
    exact ⟨T.axis.base,
      T.axis_subset_carrier T.axis.base_mem_carrier, rfl⟩
  have hend : ambientCinematicTranslation a0 b0 d0 T.axis.endpoint ∈
      cert.box.carrier := by
    apply cert.outer_le
    apply himage
    exact ⟨T.axis.endpoint,
      T.axis_subset_carrier T.axis.endpoint_mem_carrier, rfl⟩
  have hdistReal : (distortedAxisLength d0 : Real) <=
      (cert.box.diameterBound : Real) :=
    (distortedAxisLength_le_dist_transformed_endpoints T a0 b0 d0).trans
      (cert.box.dist_le_diameterBound hbase hend)
  have hdist : distortedAxisLength d0 <= cert.box.diameterBound := by
    exact_mod_cast hdistReal
  rw [FrameBox.diameterBound, Fin.sum_univ_three] at hdist
  rw [cert.side_eq] at hdist
  by_contra hlong
  push Not at hlong
  have h0 := hlong (0 : Fin 3)
  have h1 := hlong (1 : Fin 3)
  have h2 := hlong (2 : Fin 3)
  nlinarith

/-- A convex body containing a positive-radius affine tube image is
full-dimensional, proved from the surviving open ball. -/
theorem finrank_direction_affineSpan_eq_three_of_tubeImage_subset
    {K : ConvexBody Space} {delta : NNReal} (T : Tube delta)
    (a0 b0 d0 : Real) (hdelta : 0 < delta)
    (himage :
      ambientCinematicTranslation a0 b0 d0 '' T.carrier ⊆
        (K : Set Space)) :
    Module.finrank Real (affineSpan Real (K : Set Space)).direction = 3 := by
  let center := ambientCinematicTranslation a0 b0 d0 T.axis.base
  let radius := distortedTubeRadius delta d0
  have hradius : 0 < radius := distortedTubeRadius_pos hdelta d0
  have hclosed : Metric.closedBall center (radius : Real) ⊆
      (K : Set Space) :=
    (closedBall_transformedAxisBase_subset_tubeImage T a0 b0 d0).trans himage
  have hopen : Metric.ball center (radius : Real) ⊆ (K : Set Space) :=
    (Metric.ball_subset_closedBall.trans hclosed)
  have hcenter : center ∈ interior (K : Set Space) := by
    apply interior_mono hopen
    rw [Metric.isOpen_ball.interior_eq]
    exact Metric.mem_ball_self (NNReal.coe_pos.2 hradius)
  have hopenSpan : affineSpan Real (interior (K : Set Space)) = ⊤ :=
    isOpen_interior.affineSpan_eq_top ⟨center, hcenter⟩
  have hspan : affineSpan Real (K : Set Space) = ⊤ := by
    apply top_unique
    rw [← hopenSpan]
    exact affineSpan_mono Real interior_subset
  rw [hspan, AffineSubspace.direction_top, finrank_top]
  simp [Space]

/-- Fully automatic dimension-three John certificate with both transverse
and longitudinal quantitative bounds for the distorted tube. -/
theorem exists_boxDimensionsCertificate_288_with_distortedTube_bounds
    (K : ConvexBody Space) {delta : NNReal} (T : Tube delta)
    (a0 b0 d0 : Real) (hdelta : 0 < delta)
    (himage :
      ambientCinematicTranslation a0 b0 d0 '' T.carrier ⊆
        (K : Set Space)) :
    ∃ side : Fin 3 -> NNReal,
      ∃ _cert : BoxDimensionsCertificate 288 side K,
        (∀ i, 2 * distortedTubeRadius delta d0 <= side i) ∧
          ∃ j : Fin 3, distortedAxisLength d0 <= 6 * side j := by
  obtain ⟨side, ⟨cert⟩⟩ :=
    exists_boxDimensionsCertificate_288_of_finrank_direction_affineSpan_eq_three2
      K (finrank_direction_affineSpan_eq_three_of_tubeImage_subset
        T a0 b0 d0 hdelta himage)
  exact ⟨side, cert,
    fun i => FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1.BoxDimensionsCertificate.side_lower_of_tubeImage_subset T a0 b0 d0 himage cert i,
    FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1.BoxDimensionsCertificate.exists_longAxis_of_tubeImage_subset T a0 b0 d0 himage cert⟩

#print axioms inverseShearLipschitzConstant_pos
#print axioms norm_ambientCinematicTranslation_sub_le
#print axioms dist_ambientCinematicTranslation_inverse_le
#print axioms closedBall_transformedAxisPoint_subset_tubeImage
#print axioms boxCertificate_side_lower_of_closedBall_subset
#print axioms BoxDimensionsCertificate.side_lower_of_tubeImage_subset
#print axioms distortedAxisLength_le_dist_transformed_endpoints
#print axioms BoxDimensionsCertificate.exists_longAxis_of_tubeImage_subset
#print axioms finrank_direction_affineSpan_eq_three_of_tubeImage_subset
#print axioms exists_boxDimensionsCertificate_288_with_distortedTube_bounds

end

end FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
