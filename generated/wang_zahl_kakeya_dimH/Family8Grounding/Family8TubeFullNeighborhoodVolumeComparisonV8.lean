import Submission.Kakeya.ConvexFactoring.TubeSpecificLocalGrowth

/-!
# Full versus tube-truncated neighborhood volume, V8

V1--V7 are frozen elaboration/algebra drafts.  A maximal separated packing
shows that a radius-`rho` tube captures a fixed fraction of the full
`rho`-neighborhood of each of its subsets.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory Set

namespace Family8TubeFullNeighborhoodVolumeComparisonV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth

noncomputable section

theorem PackingCertificate.thickening_subset_iUnion_threeBalls
    {A : Set Space} {rho : NNReal} (P : PackingCertificate A rho) :
    Metric.thickening (rho : Real) A ⊆
      ⋃ x ∈ P.centers, Metric.ball x (((3 * rho : NNReal) : Real)) := by
  intro y hy
  obtain ⟨z, hzA, hyz⟩ := Metric.mem_thickening_iff.mp hy
  have hzCover := P.cover.subset_iUnion_closedBall hzA
  obtain ⟨x, hzCover⟩ := Set.mem_iUnion.mp hzCover
  obtain ⟨hx, hzx⟩ := Set.mem_iUnion.mp hzCover
  refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
  rw [Metric.mem_ball]
  calc
    dist y x ≤ dist y z + dist z x := dist_triangle y z x
    _ < (rho : Real) + (2 * rho : NNReal) :=
      add_lt_add_of_lt_of_le hyz hzx
    _ = ((3 * rho : NNReal) : Real) := by
      push_cast
      ring

theorem PackingCertificate.volume_thickening_le_card_smul_threeBall
    {A : Set Space} {rho : NNReal} (P : PackingCertificate A rho) :
    volume (Metric.thickening (rho : Real) A) ≤
      P.centers.card •
        volume (Metric.ball (0 : Space) (((3 * rho : NNReal) : Real))) := by
  calc
    volume (Metric.thickening (rho : Real) A) ≤
        volume (⋃ x ∈ P.centers,
          Metric.ball x (((3 * rho : NNReal) : Real))) :=
      measure_mono
        (Family8TubeFullNeighborhoodVolumeComparisonV8.PackingCertificate.thickening_subset_iUnion_threeBalls
          P)
    _ ≤ ∑ x ∈ P.centers,
        volume (Metric.ball x (((3 * rho : NNReal) : Real))) :=
      measure_biUnion_finset_le P.centers _
    _ = P.centers.card •
        volume (Metric.ball (0 : Space) (((3 * rho : NNReal) : Real))) := by
      simp [InnerProductSpace.volume_ball]

theorem volume_threeBall_eq_twoHundredSixteen_mul_halfBall (rho : NNReal) :
    volume (Metric.ball (0 : Space) (((3 * rho : NNReal) : Real))) =
      216 * volume
        (Metric.ball (0 : Space) (((rho / 2 : NNReal) : Real))) := by
  rw [EuclideanSpace.volume_ball_fin_three,
    EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_coe_nnreal]
  norm_num [ENNReal.coe_mul, ENNReal.coe_div]
  rw [mul_pow]
  have hhalf : (rho : ENNReal) / 2 =
      (rho : ENNReal) * (2 : ENNReal)⁻¹ := div_eq_mul_inv _ _
  rw [hhalf, mul_pow]
  have hthree : (3 : ENNReal) ^ 3 = 27 := by norm_num
  have hnum : ((2 : ENNReal)⁻¹) ^ 3 * 216 = 27 := by
    rw [← ENNReal.coe_inv_two]
    exact_mod_cast
      (show ((2 : NNReal)⁻¹) ^ 3 * 216 = 27 by norm_num)
  have hpi : Real.pi * 4 / 3 = Real.pi * (4 / 3) := by ring
  rw [hpi]
  calc
    _ = (rho : ENNReal) ^ 3 *
        ENNReal.ofReal (Real.pi * (4 / 3)) * 27 := by
      rw [hthree]
      ac_rfl
    _ = (rho : ENNReal) ^ 3 *
        ENNReal.ofReal (Real.pi * (4 / 3)) *
          (((2 : ENNReal)⁻¹) ^ 3 * 216) := by
      rw [hnum]
    _ = _ := by ac_rfl

theorem volume_thickening_le_twoHundredSixteen_mul_tube_inter_thickening
    {A : Set Space} {rho : NNReal} (T : Tube rho)
    (hA : A ⊆ T.carrier) (hrho : 0 < rho) :
    volume (Metric.thickening (rho : Real) A) ≤
      216 * volume
        (T.carrier ∩ Metric.thickening (rho : Real) A) := by
  obtain ⟨frame, hframe⟩ := T.exists_alignedFrame
  let B := T.alignedFrameBox frame
  have hAbox : A ⊆ B.carrier :=
    hA.trans (T.carrier_subset_alignedFrameBox frame hframe)
  let P := Classical.choice (exists_packingCertificate B hAbox rho hrho)
  have hcover :=
    Family8TubeFullNeighborhoodVolumeComparisonV8.PackingCertificate.volume_thickening_le_card_smul_threeBall
      P
  have hcapture :=
    P.card_smul_halfBallVolume_le_coarseTube_inter_thickening
      T hA hrho
  calc
    volume (Metric.thickening (rho : Real) A) ≤
        P.centers.card •
          volume (Metric.ball (0 : Space) (((3 * rho : NNReal) : Real))) :=
      hcover
    _ = 216 * (P.centers.card •
        volume (Metric.ball (0 : Space) (((rho / 2 : NNReal) : Real)))) := by
      rw [volume_threeBall_eq_twoHundredSixteen_mul_halfBall]
      simp only [nsmul_eq_mul]
      ring
    _ ≤ 216 * volume
        (T.carrier ∩ Metric.thickening (rho : Real) A) :=
      mul_le_mul_of_nonneg_left hcapture bot_le

#print axioms PackingCertificate.thickening_subset_iUnion_threeBalls
#print axioms PackingCertificate.volume_thickening_le_card_smul_threeBall
#print axioms volume_threeBall_eq_twoHundredSixteen_mul_halfBall
#print axioms
  volume_thickening_le_twoHundredSixteen_mul_tube_inter_thickening

end
end Family8TubeFullNeighborhoodVolumeComparisonV8
