import Submission.Kakeya.ConvexFactoring.TubeFrameBoxDimensions
import Submission.Kakeya.ConvexFactoring.FrameBoxInducedCoveringGrowth
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Tube-specific local capture and packing growth

This module records two direct geometric facts for the closed metric tubes used
in the Wang--Zahl setup.  A point of a `rho`-tube need not be the center of an
interior ball, but the midpoint between it and a witnessing axis point is the
center of a radius-`rho / 2` ball contained both in the tube and in the
radius-`rho` ball about the original point.  In the other direction, retaining
both short coordinates of an aligned frame box gives the local cap
`24 * delta^2 * rho` for a `delta`-tube in a radius-`3 rho` ball.

The final statements combine these two facts with an actual maximal separated
packing.  Neither local estimate nor the resulting cross-multiplied growth
bound is stored as an assumption.  These are set-level results for one
fine/coarse tube pair; this module does not claim that they have already been
assembled with parent induced-shading density or multiplicity estimates.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap
open FrameBoxInducedCoveringGrowth

noncomputable section

/-- Membership in a closed tube supplies an axis point at distance at most its
radius. -/
theorem Tube.exists_axis_point_dist_le
    {rho : ℝ≥0} (T : Tube rho) {x : Space} (hx : x ∈ T.carrier) :
    ∃ y ∈ T.axis.carrier, dist x y ≤ (rho : ℝ) := by
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (rho : ℝ) by positivity)] at hx
  simp only [mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨y, hy, hxy⟩

/-- Every point of a positive-radius tube admits a shifted half-radius ball
inside both the tube and the original radius ball. -/
theorem Tube.exists_halfRadius_ball_subset_carrier_inter_ball
    {rho : ℝ≥0} (T : Tube rho) (_hrho : 0 < rho)
    {x : Space} (hx : x ∈ T.carrier) :
    ∃ z : Space,
      Metric.ball z (((rho / 2 : ℝ≥0) : ℝ)) ⊆
        T.carrier ∩ Metric.ball x (rho : ℝ) := by
  obtain ⟨y, hy, hxy⟩ := T.exists_axis_point_dist_le hx
  let z : Space := midpoint ℝ x y
  have hzx : dist z x ≤ (rho : ℝ) / 2 := by
    calc
      dist z x = (2 : ℝ)⁻¹ * dist x y := by
        simp [z]
      _ ≤ (2 : ℝ)⁻¹ * (rho : ℝ) :=
        mul_le_mul_of_nonneg_left hxy (by positivity)
      _ = (rho : ℝ) / 2 := by ring
  have hzy : dist z y ≤ (rho : ℝ) / 2 := by
    calc
      dist z y = (2 : ℝ)⁻¹ * dist x y := by
        simp [z]
      _ ≤ (2 : ℝ)⁻¹ * (rho : ℝ) :=
        mul_le_mul_of_nonneg_left hxy (by positivity)
      _ = (rho : ℝ) / 2 := by ring
  refine ⟨z, fun q hq => ?_⟩
  have hqz : dist q z < (rho : ℝ) / 2 := by
    have := Metric.mem_ball.mp hq
    simpa [NNReal.coe_div] using this
  have hqy : dist q y < (rho : ℝ) := by
    calc
      dist q y ≤ dist q z + dist z y := dist_triangle q z y
      _ < (rho : ℝ) / 2 + (rho : ℝ) / 2 :=
        add_lt_add_of_lt_of_le hqz hzy
      _ = (rho : ℝ) := by ring
  have hqx : dist q x < (rho : ℝ) := by
    calc
      dist q x ≤ dist q z + dist z x := dist_triangle q z x
      _ < (rho : ℝ) / 2 + (rho : ℝ) / 2 :=
        add_lt_add_of_lt_of_le hqz hzx
      _ = (rho : ℝ) := by ring
  exact ⟨Metric.mem_cthickening_of_dist_le q y (rho : ℝ)
      T.axis.carrier hy hqy.le,
    Metric.mem_ball.mpr hqx⟩

/-- The shifted captured ball gives a center-independent volume lower bound
for the local tube intersection. -/
theorem Tube.ballVolume_halfRadius_le_volume_carrier_inter_ball
    {rho : ℝ≥0} (T : Tube rho) (hrho : 0 < rho)
    {x : Space} (hx : x ∈ T.carrier) :
    volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) ≤
      volume (T.carrier ∩ Metric.ball x (rho : ℝ)) := by
  obtain ⟨z, hz⟩ :=
    T.exists_halfRadius_ball_subset_carrier_inter_ball hrho hx
  calc
    volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) =
        volume (Metric.ball z (((rho / 2 : ℝ≥0) : ℝ))) := by
      simp only [InnerProductSpace.volume_ball]
    _ ≤ volume (T.carrier ∩ Metric.ball x (rho : ℝ)) := measure_mono hz

/-- The three-dimensional half-radius ball has volume at least one half of
`rho^3`.  The deliberately rational constant follows from `3 < pi`. -/
theorem half_cube_le_volume_halfRadius_ball (rho : ℝ≥0) :
    (2 : ℝ≥0∞)⁻¹ * (rho : ℝ≥0∞) ^ 3 ≤
      volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) := by
  have hpi : (4 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [← ENNReal.ofReal_ofNat 4]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_gt_three])
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hnum : (2 : ℝ≥0∞)⁻¹ ^ 3 * 4 = (2 : ℝ≥0∞)⁻¹ := by
    calc
      (2 : ℝ≥0∞)⁻¹ ^ 3 * 4 =
          ((2 : ℝ≥0∞)⁻¹ * 2) * ((2 : ℝ≥0∞)⁻¹ * 2) *
            (2 : ℝ≥0∞)⁻¹ := by ring
      _ = (2 : ℝ≥0∞)⁻¹ := by rw [htwo]; simp
  rw [EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_coe_nnreal]
  have hcoeff :
      (2 : ℝ≥0∞)⁻¹ * (rho : ℝ≥0∞) ^ 3 =
        (((rho / 2 : ℝ≥0) : ℝ≥0∞)) ^ 3 * 4 := by
    rw [ENNReal.coe_div (by norm_num), ENNReal.coe_ofNat,
      div_eq_mul_inv, mul_pow]
    calc
      (2 : ℝ≥0∞)⁻¹ * (rho : ℝ≥0∞) ^ 3 =
          (rho : ℝ≥0∞) ^ 3 * (2 : ℝ≥0∞)⁻¹ := by ac_rfl
      _ = (rho : ℝ≥0∞) ^ 3 * ((2 : ℝ≥0∞)⁻¹ ^ 3 * 4) := by
        rw [hnum]
      _ = ((rho : ℝ≥0∞) ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ 3) * 4 := by
        ac_rfl
  rw [hcoeff]
  exact mul_le_mul_of_nonneg_left hpi bot_le

/-- Coordinate center for a ball cut which retains the first two frame-box
coordinates and centers only the axial coordinate at the ball center. -/
def FrameBox.axialBallIntersectionCenter (B : FrameBox) (x : Space) : Coord :=
  ![B.coordinateCenter 0, B.coordinateCenter 1, ⟪B.frame 2, x⟫_ℝ]

/-- Half-widths for the corresponding two-short-axis coordinate window. -/
def FrameBox.axialBallIntersectionHalf
    (B : FrameBox) (r : ℝ≥0) : Fin 3 → ℝ≥0 :=
  ![B.coordinateHalf 0, B.coordinateHalf 1, r]

/-- A frame box cut by a radius-`r` ball lies in a window of full widths
`side 0`, `side 1`, and `2r`. -/
theorem FrameBox.carrier_inter_ball_subset_axialCoordinateWindow
    (B : FrameBox) (x : Space) (r : ℝ≥0) :
    B.carrier ∩ Metric.ball x (r : ℝ) ⊆
      centeredCoordinateWindow B.frame (B.axialBallIntersectionCenter x)
        (B.axialBallIntersectionHalf r) := by
  intro y hy
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  fin_cases i
  · simpa [FrameBox.axialBallIntersectionCenter,
      FrameBox.axialBallIntersectionHalf, FrameBox.coordinateCenter,
      FrameBox.coordinateHalf] using
      B.centeredCoordinate_abs_le_halfSide hy.1 0
  · simpa [FrameBox.axialBallIntersectionCenter,
      FrameBox.axialBallIntersectionHalf, FrameBox.coordinateCenter,
      FrameBox.coordinateHalf] using
      B.centeredCoordinate_abs_le_halfSide hy.1 1
  · change |⟪B.frame 2, y⟫_ℝ - ⟪B.frame 2, x⟫_ℝ| ≤ (r : ℝ)
    exact (abs_inner_sub_inner_le_dist_of_norm_eq_one
      (B.frame 2) y x (B.frame.norm_eq_one 2)).trans
        (Metric.mem_ball.mp hy.2).le

/-- Exact volume of the two-short-axis coordinate window. -/
theorem FrameBox.volume_axialBallIntersectionCoordinateWindow
    (B : FrameBox) (x : Space) (r : ℝ≥0) :
    volume (centeredCoordinateWindow B.frame
      (B.axialBallIntersectionCenter x) (B.axialBallIntersectionHalf r)) =
      (2 * (B.coordinateHalf 0 : ℝ≥0∞)) *
        (2 * (B.coordinateHalf 1 : ℝ≥0∞)) *
          (2 * (r : ℝ≥0∞)) := by
  rw [volume_centeredCoordinateWindow_orthonormalBasis, Fin.prod_univ_three]
  simp [FrameBox.axialBallIntersectionHalf]

/-- Local cap retaining both short side lengths of an arbitrary frame box. -/
theorem FrameBox.volume_carrier_inter_ball_le_axialCap
    (B : FrameBox) (x : Space) (r : ℝ≥0) :
    volume (B.carrier ∩ Metric.ball x (r : ℝ)) ≤
      (2 * (B.coordinateHalf 0 : ℝ≥0∞)) *
        (2 * (B.coordinateHalf 1 : ℝ≥0∞)) *
          (2 * (r : ℝ≥0∞)) := by
  rw [← B.volume_axialBallIntersectionCoordinateWindow x r]
  exact measure_mono (B.carrier_inter_ball_subset_axialCoordinateWindow x r)

/-- The aligned box gives the scale-free local tube cap
`8 * delta^2 * r`. -/
theorem Tube.volume_carrier_inter_ball_le_eight_mul_sq_mul
    {delta : ℝ≥0} (T : Tube delta) (x : Space) (r : ℝ≥0) :
    volume (T.carrier ∩ Metric.ball x (r : ℝ)) ≤
      8 * (delta : ℝ≥0∞) ^ 2 * (r : ℝ≥0∞) := by
  obtain ⟨frame, hframe⟩ := T.exists_alignedFrame
  let B := T.alignedFrameBox frame
  calc
    volume (T.carrier ∩ Metric.ball x (r : ℝ)) ≤
        volume (B.carrier ∩ Metric.ball x (r : ℝ)) :=
      measure_mono (inter_subset_inter_left _
        (T.carrier_subset_alignedFrameBox frame hframe))
    _ ≤ (2 * (B.coordinateHalf 0 : ℝ≥0∞)) *
          (2 * (B.coordinateHalf 1 : ℝ≥0∞)) *
            (2 * (r : ℝ≥0∞)) :=
      B.volume_carrier_inter_ball_le_axialCap x r
    _ = 8 * (delta : ℝ≥0∞) ^ 2 * (r : ℝ≥0∞) := by
      simp [B, FrameBox.coordinateHalf, Tube.alignedFrameBox,
        Tube.frameBoxSides]
      ring

/-- A `delta`-tube in a radius-`3 rho` ball has volume at most
`24 * delta^2 * rho`.  The estimate itself is valid without comparing the two
scales. -/
theorem Tube.volume_carrier_inter_threeBall_le
    {delta rho : ℝ≥0} (T : Tube delta) (x : Space) :
    volume (T.carrier ∩ Metric.ball x (((3 * rho : ℝ≥0) : ℝ))) ≤
      24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞) := by
  obtain ⟨frame, hframe⟩ := T.exists_alignedFrame
  let B := T.alignedFrameBox frame
  calc
    volume (T.carrier ∩ Metric.ball x (((3 * rho : ℝ≥0) : ℝ))) ≤
        volume (B.carrier ∩ Metric.ball x (((3 * rho : ℝ≥0) : ℝ))) :=
      measure_mono (inter_subset_inter_left _
        (T.carrier_subset_alignedFrameBox frame hframe))
    _ ≤ (2 * (B.coordinateHalf 0 : ℝ≥0∞)) *
          (2 * (B.coordinateHalf 1 : ℝ≥0∞)) *
            (2 * ((3 * rho : ℝ≥0) : ℝ≥0∞)) :=
      B.volume_carrier_inter_ball_le_axialCap x (3 * rho)
    _ = 24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞) := by
      simp [B, FrameBox.coordinateHalf, Tube.alignedFrameBox,
        Tube.frameBoxSides, ENNReal.coe_mul]
      ring

/-- Scale-ordered version of the tube cap used in the packing application. -/
theorem Tube.volume_carrier_inter_threeBall_le_of_le
    {delta rho : ℝ≥0} (T : Tube delta) (_hdelta : delta ≤ rho)
    (x : Space) :
    volume (T.carrier ∩ Metric.ball x (((3 * rho : ℝ≥0) : ℝ))) ≤
      24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞) :=
  T.volume_carrier_inter_threeBall_le x

/-- Local coarse-tube pieces inherit pairwise disjointness from the packing
balls. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.coarseTubePieces_pairwiseDisjoint
    {A : Set Space} {rho : ℝ≥0} (P : PackingCertificate A rho)
    (T : Tube rho) :
    Set.PairwiseDisjoint (↑P.centers : Set Space)
      (fun x => T.carrier ∩ Metric.ball x (rho : ℝ)) := by
  exact P.smallBalls_pairwiseDisjoint.mono_on
    (fun _x _hx => inter_subset_right)

/-- The union of local coarse-tube pieces lies in the part of the thickening
which remains inside that coarse tube. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.iUnion_coarseTubePieces_subset_inter_thickening
    {A : Set Space} {rho : ℝ≥0} (P : PackingCertificate A rho)
    (T : Tube rho) :
    (⋃ x ∈ P.centers, T.carrier ∩ Metric.ball x (rho : ℝ)) ⊆
      T.carrier ∩ Metric.thickening (rho : ℝ) A := by
  refine Set.iUnion₂_subset fun x hx => ?_
  intro y hy
  exact ⟨hy.1,
    Metric.ball_subset_thickening (P.centers_subset hx) (rho : ℝ) hy.2⟩

/-- Each packing center captures a half-radius ball inside the coarse tube;
summing the disjoint local pieces gives the corresponding volume lower bound. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.card_smul_halfBallVolume_le_coarseTube_inter_thickening
    {A : Set Space} {rho : ℝ≥0} (P : PackingCertificate A rho)
    (T : Tube rho) (hA : A ⊆ T.carrier) (hrho : 0 < rho) :
    P.centers.card •
        volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) ≤
      volume (T.carrier ∩ Metric.thickening (rho : ℝ) A) := by
  calc
    P.centers.card •
        volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) =
        ∑ x ∈ P.centers,
          volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) := by
      simp
    _ ≤ ∑ x ∈ P.centers,
        volume (T.carrier ∩ Metric.ball x (rho : ℝ)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact T.ballVolume_halfRadius_le_volume_carrier_inter_ball hrho
        (hA (P.centers_subset hx))
    _ = volume (⋃ x ∈ P.centers,
        T.carrier ∩ Metric.ball x (rho : ℝ)) := by
      symm
      exact measure_biUnion_finset
        (P.coarseTubePieces_pairwiseDisjoint T)
        (fun _x _hx => T.isCompact_carrier.measurableSet.inter measurableSet_ball)
    _ ≤ volume (T.carrier ∩ Metric.thickening (rho : ℝ) A) :=
      measure_mono (P.iUnion_coarseTubePieces_subset_inter_thickening T)

/-- The large packing balls and the genuine two-short-axis tube cap bound the
packed set by the number of centers. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.volume_le_card_smul_tubeCap
    {A : Set Space} {delta rho : ℝ≥0}
    (P : PackingCertificate A rho) (T : Tube delta)
    (hA : A ⊆ T.carrier) (hdelta : delta ≤ rho) (hrho : 0 < rho) :
    volume A ≤
      P.centers.card •
        (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) := by
  calc
    volume A ≤ volume (⋃ x ∈ P.centers,
        T.carrier ∩ Metric.ball x (((3 * rho : ℝ≥0) : ℝ))) := by
      apply measure_mono
      intro y hy
      have hyCover := P.subset_iUnion_largeBalls hrho hy
      obtain ⟨x, hyCover⟩ := Set.mem_iUnion.mp hyCover
      obtain ⟨hx, hyx⟩ := Set.mem_iUnion.mp hyCover
      exact Set.mem_iUnion.mpr ⟨x,
        Set.mem_iUnion.mpr ⟨hx, hA hy, hyx⟩⟩
    _ ≤ ∑ x ∈ P.centers,
        volume (T.carrier ∩ Metric.ball x (((3 * rho : ℝ≥0) : ℝ))) :=
      measure_biUnion_finset_le P.centers _
    _ ≤ ∑ _x ∈ P.centers,
        (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact T.volume_carrier_inter_threeBall_le_of_le hdelta x
    _ = P.centers.card •
        (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) := by simp

/-- Division-free tube-specific packing growth.  The fine tube supplies the
`delta^2 rho` cap, while the coarse tube captures a genuine half-radius ball
at every packing center. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.volume_mul_halfBallVolume_le_tubeCap_mul_inter_thickening
    {A : Set Space} {delta rho : ℝ≥0}
    (P : PackingCertificate A rho) (fine : Tube delta) (coarse : Tube rho)
    (hAfine : A ⊆ fine.carrier) (hAcoarse : A ⊆ coarse.carrier)
    (hdelta : delta ≤ rho) (hrho : 0 < rho) :
    volume A *
        volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) ≤
      (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) *
        volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) := by
  calc
    volume A *
        volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) ≤
        (P.centers.card •
          (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞))) *
            volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) :=
      mul_le_mul_of_nonneg_right
        (P.volume_le_card_smul_tubeCap fine hAfine hdelta hrho) bot_le
    _ = (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) *
        (P.centers.card •
          volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ)))) := by
      simp only [nsmul_eq_mul]
      ac_rfl
    _ ≤ (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) *
        volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) :=
      mul_le_mul_of_nonneg_left
        (P.card_smul_halfBallVolume_le_coarseTube_inter_thickening
          coarse hAcoarse hrho) bot_le

/-- After inserting the explicit three-dimensional ball volume and cancelling
the positive finite scale `rho`, the packing estimate takes the Wang--Zahl
cross-multiplied form with constant `48`. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.volume_mul_sq_le_fortyEight_mul_sq_mul_inter_thickening
    {A : Set Space} {delta rho : ℝ≥0}
    (P : PackingCertificate A rho) (fine : Tube delta) (coarse : Tube rho)
    (hAfine : A ⊆ fine.carrier) (hAcoarse : A ⊆ coarse.carrier)
    (_hdeltaPos : 0 < delta) (hrho : 0 < rho) (hdelta : delta ≤ rho) :
    volume A * (rho : ℝ≥0∞) ^ 2 ≤
      48 * (delta : ℝ≥0∞) ^ 2 *
        volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) := by
  have hsmall :
      volume A * ((2 : ℝ≥0∞)⁻¹ * (rho : ℝ≥0∞) ^ 3) ≤
        (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) *
          volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) := by
    calc
      volume A * ((2 : ℝ≥0∞)⁻¹ * (rho : ℝ≥0∞) ^ 3) ≤
          volume A *
            volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (half_cube_le_volume_halfRadius_ball rho) bot_le
      _ ≤ (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) *
          volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) :=
        P.volume_mul_halfBallVolume_le_tubeCap_mul_inter_thickening
          fine coarse hAfine hAcoarse hdelta hrho
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hsmall (show (0 : ℝ≥0∞) ≤ 2 by exact bot_le)
  have hfactored :
      (volume A * (rho : ℝ≥0∞) ^ 2) * (rho : ℝ≥0∞) ≤
        (48 * (delta : ℝ≥0∞) ^ 2 *
          volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A)) *
            (rho : ℝ≥0∞) := by
    calc
      (volume A * (rho : ℝ≥0∞) ^ 2) * (rho : ℝ≥0∞) =
          volume A * (rho : ℝ≥0∞) ^ 3 := by ring
      _ = (volume A * ((2 : ℝ≥0∞)⁻¹ * (rho : ℝ≥0∞) ^ 3)) * 2 := by
        calc
          volume A * (rho : ℝ≥0∞) ^ 3 =
              volume A * (rho : ℝ≥0∞) ^ 3 *
                ((2 : ℝ≥0∞)⁻¹ * 2) := by rw [htwo, mul_one]
          _ = _ := by ring
      _ ≤ ((24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) *
          volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A)) * 2 :=
        hmul
      _ = (48 * (delta : ℝ≥0∞) ^ 2 *
          volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A)) *
            (rho : ℝ≥0∞) := by ring
  have hrho0 : (rho : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hrho.ne'
  have hrhoTop : (rho : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hrhoCancel :
      (rho : ℝ≥0∞) * (rho : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hrho0 hrhoTop
  calc
    volume A * (rho : ℝ≥0∞) ^ 2 =
        ((volume A * (rho : ℝ≥0∞) ^ 2) * (rho : ℝ≥0∞)) *
          (rho : ℝ≥0∞)⁻¹ := by
      rw [mul_assoc, hrhoCancel, mul_one]
    _ ≤ ((48 * (delta : ℝ≥0∞) ^ 2 *
          volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A)) *
            (rho : ℝ≥0∞)) * (rho : ℝ≥0∞)⁻¹ :=
      mul_le_mul_of_nonneg_right hfactored bot_le
    _ = 48 * (delta : ℝ≥0∞) ^ 2 *
        volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) := by
      rw [mul_assoc, hrhoCancel, mul_one]

/-- A maximal separated set supplies actual packing data and the preceding
tube-specific cross-growth inequality. -/
theorem exists_packingCertificate_with_tubeCrossGrowth
    {A : Set Space} {delta rho : ℝ≥0}
    (fine : Tube delta) (coarse : Tube rho)
    (hAfine : A ⊆ fine.carrier) (hAcoarse : A ⊆ coarse.carrier)
    (hdelta : delta ≤ rho) (hrho : 0 < rho) :
    ∃ P : PackingCertificate A rho,
      P.centers.card •
          volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) ≤
        volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) ∧
      volume A *
          volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) ≤
        (24 * (delta : ℝ≥0∞) ^ 2 * (rho : ℝ≥0∞)) *
          volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) := by
  obtain ⟨frame, hframe⟩ := fine.exists_alignedFrame
  let B := fine.alignedFrameBox frame
  have hAbox : A ⊆ B.carrier :=
    hAfine.trans (fine.carrier_subset_alignedFrameBox frame hframe)
  let P := Classical.choice (exists_packingCertificate B hAbox rho hrho)
  exact ⟨P,
    P.card_smul_halfBallVolume_le_coarseTube_inter_thickening
      coarse hAcoarse hrho,
    P.volume_mul_halfBallVolume_le_tubeCap_mul_inter_thickening
      fine coarse hAfine hAcoarse hdelta hrho⟩

/-- Actual maximal-separated packing data with both G3 capture and the
explicit G4 `48 * delta^2` cross-growth estimate. -/
theorem exists_packingCertificate_with_explicit_tubeCrossGrowth
    {A : Set Space} {delta rho : ℝ≥0}
    (fine : Tube delta) (coarse : Tube rho)
    (hAfine : A ⊆ fine.carrier) (hAcoarse : A ⊆ coarse.carrier)
    (hdeltaPos : 0 < delta) (hrho : 0 < rho) (hdelta : delta ≤ rho) :
    ∃ P : PackingCertificate A rho,
      P.centers.card •
          volume (Metric.ball (0 : Space) (((rho / 2 : ℝ≥0) : ℝ))) ≤
        volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) ∧
      volume A * (rho : ℝ≥0∞) ^ 2 ≤
        48 * (delta : ℝ≥0∞) ^ 2 *
          volume (coarse.carrier ∩ Metric.thickening (rho : ℝ) A) := by
  obtain ⟨frame, hframe⟩ := fine.exists_alignedFrame
  let B := fine.alignedFrameBox frame
  have hAbox : A ⊆ B.carrier :=
    hAfine.trans (fine.carrier_subset_alignedFrameBox frame hframe)
  let P := Classical.choice (exists_packingCertificate B hAbox rho hrho)
  exact ⟨P,
    P.card_smul_halfBallVolume_le_coarseTube_inter_thickening
      coarse hAcoarse hrho,
    P.volume_mul_sq_le_fortyEight_mul_sq_mul_inter_thickening
      fine coarse hAfine hAcoarse hdeltaPos hrho hdelta⟩

end

end Submission.Kakeya.ConvexGeometry
