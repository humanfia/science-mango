import «CubeWeightMaster»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open BallwiseLocalVolumeUniformization
open CubeWeightUniformization
open CubeWeightMaster

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace ExactRadiusCellAdapter

/-! The target radius is `rho`.  The packing cells below are built with cover
radius `rho / 2`, hence with packing radius `(rho / 2) / 3`. -/

def cellNeighbors {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3))
    (selected : Finset (Fin C.centers.card)) (x : Space) :
    Finset (Fin C.centers.card) :=
  selected.filter fun q ↦
    (packingCellFin C q ∩ Metric.ball x (rho : ℝ)).Nonempty

theorem packingCellFin_subset_targetBall
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3))
    (q : Fin C.centers.card) {x : Space}
    (hx : x ∈ packingCellFin C q) :
    packingCellFin C q ⊆ Metric.ball x (rho : ℝ) := by
  intro y hy
  have hxc := packingCellFin_subset_centerBall C q hx
  have hyc := packingCellFin_subset_centerBall C q hy
  rw [Metric.mem_ball] at hxc hyc ⊢
  have hxc' : dist (packingCenterAt C q.1) x < (rho : ℝ) / 2 := by
    rw [dist_comm]
    simpa [NNReal.coe_div] using hxc
  calc
    dist y x ≤ dist y (packingCenterAt C q.1) +
        dist (packingCenterAt C q.1) x := dist_triangle _ _ _
    _ < (rho : ℝ) / 2 + (rho : ℝ) / 2 := by
      exact add_lt_add (by simpa [NNReal.coe_div] using hyc) hxc'
    _ = (rho : ℝ) := by ring

theorem center_mem_three_halves_ball_of_mem_cellNeighbors
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3))
    (selected : Finset (Fin C.centers.card)) (x : Space)
    {q : Fin C.centers.card} (hq : q ∈ cellNeighbors C selected x) :
    packingCenterAt C q.1 ∈ Metric.ball x ((3 / 2 : ℝ) * rho) := by
  obtain ⟨y, hycell, hyball⟩ := (Finset.mem_filter.mp hq).2
  have hyc := packingCellFin_subset_centerBall C q hycell
  rw [Metric.mem_ball] at hyc hyball ⊢
  calc
    dist (packingCenterAt C q.1) x ≤
        dist (packingCenterAt C q.1) y + dist y x := dist_triangle _ _ _
    _ < (rho : ℝ) / 2 + (rho : ℝ) := by
      exact add_lt_add (by simpa [dist_comm, NNReal.coe_div] using hyc) hyball
    _ = (3 / 2 : ℝ) * rho := by ring

theorem smallBall_subset_bigBall_of_mem_cellNeighbors
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3))
    (selected : Finset (Fin C.centers.card)) (x : Space)
    {q : Fin C.centers.card} (hq : q ∈ cellNeighbors C selected x) :
    Metric.ball (packingCenterAt C q.1) ((((rho / 2) / 3 : ℝ≥0) : ℝ)) ⊆
      Metric.ball x ((5 / 3 : ℝ) * rho) := by
  intro y hy
  have hc := center_mem_three_halves_ball_of_mem_cellNeighbors C selected x hq
  rw [Metric.mem_ball] at hy hc ⊢
  calc
    dist y x ≤ dist y (packingCenterAt C q.1) +
        dist (packingCenterAt C q.1) x := dist_triangle _ _ _
    _ < ((((rho / 2) / 3 : ℝ≥0) : ℝ)) + (3 / 2 : ℝ) * rho :=
      add_lt_add hy hc
    _ = (5 / 3 : ℝ) * rho := by
      norm_num [NNReal.coe_mul, NNReal.coe_div]
      ring_nf

theorem packingCenterAt_mem_centers
    {A : Set Space} {s : ℝ≥0} (C : PackingCertificate A (s / 3))
    (q : Fin C.centers.card) : packingCenterAt C q.1 ∈ C.centers := by
  simp [packingCenterAt, q.2]

theorem packingCenterAt_injective
    {A : Set Space} {s : ℝ≥0} (C : PackingCertificate A (s / 3)) :
    Function.Injective (fun q : Fin C.centers.card ↦ packingCenterAt C q.1) := by
  intro q r hqr
  have hq : packingCenterAt C q.1 = ((C.centers.equivFin).symm q : C.centers).1 := by
    simp [packingCenterAt, q.2]
  have hr : packingCenterAt C r.1 = ((C.centers.equivFin).symm r : C.centers).1 := by
    simp [packingCenterAt, r.2]
  apply (C.centers.equivFin).symm.injective
  apply Subtype.ext
  simpa [hq, hr] using hqr

theorem neighbor_smallBalls_pairwiseDisjoint
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3))
    (selected : Finset (Fin C.centers.card)) (x : Space) :
    Set.PairwiseDisjoint (↑(cellNeighbors C selected x) : Set (Fin C.centers.card))
      (fun q ↦ Metric.ball (packingCenterAt C q.1)
        ((((rho / 2) / 3 : ℝ≥0) : ℝ))) := by
  intro q hq r hr hqr
  apply C.smallBalls_pairwiseDisjoint
    (packingCenterAt_mem_centers C q) (packingCenterAt_mem_centers C r)
  exact fun h ↦ hqr (packingCenterAt_injective C h)

theorem neighbor_card_smul_smallBallVolume_le_bigBall
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3))
    (selected : Finset (Fin C.centers.card)) (x : Space) :
    (cellNeighbors C selected x).card •
        volume (Metric.ball (0 : Space) ((((rho / 2) / 3 : ℝ≥0) : ℝ))) ≤
      volume (Metric.ball x ((5 / 3 : ℝ) * rho)) := by
  calc
    (cellNeighbors C selected x).card •
        volume (Metric.ball (0 : Space) ((((rho / 2) / 3 : ℝ≥0) : ℝ))) =
        ∑ q ∈ cellNeighbors C selected x,
          volume (Metric.ball (packingCenterAt C q.1)
            ((((rho / 2) / 3 : ℝ≥0) : ℝ))) := by
      simp [InnerProductSpace.volume_ball]
    _ = volume (⋃ q ∈ cellNeighbors C selected x,
          Metric.ball (packingCenterAt C q.1)
            ((((rho / 2) / 3 : ℝ≥0) : ℝ))) := by
      symm
      exact measure_biUnion_finset
        (neighbor_smallBalls_pairwiseDisjoint C selected x)
        (fun _ _ ↦ measurableSet_ball)
    _ ≤ volume (Metric.ball x ((5 / 3 : ℝ) * rho)) := by
      apply measure_mono
      exact Set.iUnion₂_subset fun q hq ↦
        smallBall_subset_bigBall_of_mem_cellNeighbors C selected x hq

theorem bigBallVolume_eq_1000_smul_smallBallVolume (rho : ℝ≥0) :
    volume (Metric.ball (0 : Space) ((5 / 3 : ℝ) * rho)) =
      1000 • volume
        (Metric.ball (0 : Space) ((((rho / 2) / 3 : ℝ≥0) : ℝ))) := by
  simp only [EuclideanSpace.volume_ball_fin_three, nsmul_eq_mul]
  simp only [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_mul (by positivity : 0 ≤ (5 / 3 : ℝ))]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  norm_num [NNReal.coe_mul, NNReal.coe_div]
  ring

theorem cellNeighbors_card_le_1000
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3)) (hrho : 0 < rho)
    (selected : Finset (Fin C.centers.card)) (x : Space) :
    (cellNeighbors C selected x).card ≤ 1000 := by
  have h := neighbor_card_smul_smallBallVolume_le_bigBall C selected x
  rw [show volume (Metric.ball x ((5 / 3 : ℝ) * rho)) =
      volume (Metric.ball (0 : Space) ((5 / 3 : ℝ) * rho)) by
        simp [InnerProductSpace.volume_ball],
    bigBallVolume_eq_1000_smul_smallBallVolume] at h
  simp only [nsmul_eq_mul] at h
  have hvol0 : volume
      (Metric.ball (0 : Space) ((((rho / 2) / 3 : ℝ≥0) : ℝ))) ≠ 0 := by
    rw [EuclideanSpace.volume_ball_fin_three]
    positivity
  have hvoltop : volume
      (Metric.ball (0 : Space) ((((rho / 2) / 3 : ℝ≥0) : ℝ))) ≠ ∞ := by
    rw [EuclideanSpace.volume_ball_fin_three]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hcardENN : ((cellNeighbors C selected x).card : ℝ≥0∞) ≤ 1000 :=
    (ENNReal.mul_le_mul_iff_right hvol0 hvoltop).mp
      (by simpa [mul_comm] using h)
  exact_mod_cast hcardENN

theorem selectedCell_inter_ball_subset_iUnion_neighbors
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3))
    (selected : Finset (Fin C.centers.card)) (U : Set Space) (x : Space) :
    (U ∩ selectedRegion (packingCellFin C) selected) ∩ Metric.ball x (rho : ℝ) ⊆
      ⋃ q ∈ cellNeighbors C selected x, U ∩ packingCellFin C q := by
  intro y hy
  obtain ⟨q, hyq⟩ := Set.mem_iUnion.mp hy.1.2
  obtain ⟨hq, hycell⟩ := Set.mem_iUnion.mp hyq
  have hneighbor : q ∈ cellNeighbors C selected x := by
    apply Finset.mem_filter.mpr
    exact ⟨hq, ⟨y, hycell, hy.2⟩⟩
  exact Set.mem_iUnion.mpr ⟨q,
    Set.mem_iUnion.mpr ⟨hneighbor, hy.1.1, hycell⟩⟩

theorem exactRadius_upper_of_cellBand
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3)) (hrho : 0 < rho)
    (selected : Finset (Fin C.centers.card)) (U : Set Space) (w : ℝ≥0∞)
    (hupper : ∀ q ∈ selected, volume (U ∩ packingCellFin C q) < 2 * w)
    (x : Space) :
    volume ((U ∩ selectedRegion (packingCellFin C) selected) ∩
        Metric.ball x (rho : ℝ)) ≤ 2000 * w := by
  calc
    volume ((U ∩ selectedRegion (packingCellFin C) selected) ∩
        Metric.ball x (rho : ℝ)) ≤
        volume (⋃ q ∈ cellNeighbors C selected x,
          U ∩ packingCellFin C q) :=
      measure_mono (selectedCell_inter_ball_subset_iUnion_neighbors C selected U x)
    _ ≤ ∑ q ∈ cellNeighbors C selected x,
        volume (U ∩ packingCellFin C q) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ cellNeighbors C selected x, 2 * w := by
      apply Finset.sum_le_sum
      intro q hq
      exact (hupper q (Finset.mem_filter.mp hq).1).le
    _ = (cellNeighbors C selected x).card * (2 * w) := by simp
    _ ≤ 1000 * (2 * w) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast cellNeighbors_card_le_1000 C hrho selected x
      · exact bot_le
    _ = 2000 * w := by ring

theorem exactRadius_lower_of_ownerCell
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3))
    (selected : Finset (Fin C.centers.card)) (U : Set Space) (w : ℝ≥0∞)
    (hlower : ∀ q ∈ selected, w ≤ volume (U ∩ packingCellFin C q))
    {x : Space} (hx : x ∈ selectedRegion (packingCellFin C) selected) :
    w ≤ volume ((U ∩ selectedRegion (packingCellFin C) selected) ∩
      Metric.ball x (rho : ℝ)) := by
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hq, hxcell⟩ := Set.mem_iUnion.mp hxq
  calc
    w ≤ volume (U ∩ packingCellFin C q) := hlower q hq
    _ ≤ volume ((U ∩ selectedRegion (packingCellFin C) selected) ∩
        Metric.ball x (rho : ℝ)) := by
      apply measure_mono
      intro y hy
      exact ⟨⟨hy.1, cell_subset_selectedRegion (packingCellFin C) selected hq hy.2⟩,
        packingCellFin_subset_targetBall C q hxcell hy.2⟩

theorem exactRadius_band_of_cellBand
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3)) (hrho : 0 < rho)
    (selected : Finset (Fin C.centers.card)) (U : Set Space) (w : ℝ≥0∞)
    (hband : ∀ q ∈ selected,
      w ≤ volume (U ∩ packingCellFin C q) ∧
        volume (U ∩ packingCellFin C q) < 2 * w) :
    ∀ x ∈ selectedRegion (packingCellFin C) selected,
      w ≤ volume ((U ∩ selectedRegion (packingCellFin C) selected) ∩
          Metric.ball x (rho : ℝ)) ∧
        volume ((U ∩ selectedRegion (packingCellFin C) selected) ∩
          Metric.ball x (rho : ℝ)) ≤ 2000 * w := by
  intro x hx
  exact ⟨exactRadius_lower_of_ownerCell C selected U w
      (fun q hq ↦ (hband q hq).1) hx,
    exactRadius_upper_of_cellBand C hrho selected U w
      (fun q hq ↦ (hband q hq).2) x⟩

end ExactRadiusCellAdapter

end

end Submission.Kakeya.ConvexFactoring

#print axioms Submission.Kakeya.ConvexFactoring.ExactRadiusCellAdapter.exactRadius_band_of_cellBand
