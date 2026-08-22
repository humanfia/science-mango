import Submission.Kakeya.ConvexFactoring.FrameBoxBallIntersection
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Packing data and frame-box covering growth

The centers below are the actual finite maximal separated set supplied by
Mathlib.  The final estimate is derived from its cover and separation
properties together with `FrameBox.volume_carrier_inter_ball_le`; it is not
stored as a hypothesis in the packing data.  This is a set-level covering
estimate; it does not by itself construct an induced shading or prove the final
scale-normalized Wang--Zahl estimate.
-/

namespace FrameBoxInducedCoveringGrowth

/-- Finite packing data at scale `r`.  Separation is at scale `2r`, hence the
open `r`-balls are disjoint, while maximality gives a closed `2r`-cover. -/
structure PackingCertificate (A : Set Space) (r : ℝ≥0) where
  centers : Finset Space
  centers_subset : (↑centers : Set Space) ⊆ A
  separated : Metric.IsSeparated (2 * r) (↑centers : Set Space)
  cover : Metric.IsCover (2 * r) A (↑centers : Set Space)

/-- The concrete frame-box cap for a ball of radius `s`. -/
def localBallCap (B : FrameBox) (s : ℝ≥0) : ℝ≥0∞ :=
  (2 * (B.coordinateHalf 0 : ℝ≥0∞)) *
    (2 * (s : ℝ≥0∞)) * (2 * (s : ℝ≥0∞))

/-- Compact containment makes the relevant packing number finite. -/
theorem packingNumber_two_mul_ne_top
    (B : FrameBox) {A : Set Space} (hA : A ⊆ B.carrier)
    (r : ℝ≥0) (hr : 0 < r) :
    Metric.packingNumber (2 * r) A ≠ ⊤ := by
  have htot : TotallyBounded A :=
    B.isCompact_carrier.totallyBounded.subset hA
  obtain ⟨N, _hNsub, hNfinite, hNcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded
      (ε := r) hr.ne' htot
  have hext_lt_top : Metric.externalCoveringNumber r A < ⊤ :=
    hNcover.externalCoveringNumber_le_encard.trans_lt hNfinite.encard_lt_top
  exact ((Metric.packingNumber_two_mul_le_externalCoveringNumber r A).trans_lt
    hext_lt_top).ne

/-- The maximal separated set produces actual finite packing data. -/
theorem exists_packingCertificate
    (B : FrameBox) {A : Set Space} (hA : A ⊆ B.carrier)
    (r : ℝ≥0) (hr : 0 < r) :
    Nonempty (PackingCertificate A r) := by
  have hpack : Metric.packingNumber (2 * r) A ≠ ⊤ :=
    packingNumber_two_mul_ne_top B hA r hr
  let S : Set Space := Metric.maximalSeparatedSet (2 * r) A
  have hSfinite : S.Finite := by
    rw [← Set.encard_lt_top_iff]
    rw [show S.encard = Metric.packingNumber (2 * r) A by
      simpa [S] using Metric.encard_maximalSeparatedSet hpack]
    exact hpack.lt_top
  refine ⟨{
    centers := hSfinite.toFinset
    centers_subset := ?_
    separated := ?_
    cover := ?_ }⟩
  · simpa [S] using (Metric.maximalSeparatedSet_subset :
      Metric.maximalSeparatedSet (2 * r) A ⊆ A)
  · simpa [S] using
      (Metric.isSeparated_maximalSeparatedSet :
        Metric.IsSeparated (2 * r)
          (Metric.maximalSeparatedSet (2 * r) A : Set Space))
  · simpa [S] using Metric.isCover_maximalSeparatedSet hpack

/-- Separation at `2r` gives pairwise disjoint open balls of radius `r`. -/
theorem PackingCertificate.smallBalls_pairwiseDisjoint
    {A : Set Space} {r : ℝ≥0} (C : PackingCertificate A r) :
    Set.PairwiseDisjoint (↑C.centers : Set Space)
      (fun x => Metric.ball x (r : ℝ)) := by
  intro x hx y hy hxy
  change Disjoint (Metric.ball x (r : ℝ)) (Metric.ball y (r : ℝ))
  apply Metric.ball_disjoint_ball
  have hsep := C.separated hx hy hxy
  have hdist : (2 : ℝ) * (r : ℝ) < dist x y := by
    have hsep' : ((2 * r : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal (dist x y) := by
      simpa [edist_dist] using hsep
    simpa using ENNReal.coe_lt_ofReal.mp hsep'
  calc
    (r : ℝ) + (r : ℝ) = 2 * (r : ℝ) := by ring
    _ ≤ dist x y := hdist.le

/-- Every small packing ball lies in the `r`-thickening of the packed set. -/
theorem PackingCertificate.iUnion_smallBalls_subset_thickening
    {A : Set Space} {r : ℝ≥0} (C : PackingCertificate A r) :
    (⋃ x ∈ C.centers, Metric.ball x (r : ℝ)) ⊆
      Metric.thickening (r : ℝ) A := by
  refine Set.iUnion₂_subset fun x hx => ?_
  exact Metric.ball_subset_thickening (C.centers_subset hx) (r : ℝ)

/-- The disjoint small balls give a lower bound for the thickening volume. -/
theorem PackingCertificate.card_smul_ballVolume_le_thickening
    {A : Set Space} {r : ℝ≥0} (C : PackingCertificate A r) :
    C.centers.card • volume (Metric.ball (0 : Space) (r : ℝ)) ≤
      volume (Metric.thickening (r : ℝ) A) := by
  calc
    C.centers.card • volume (Metric.ball (0 : Space) (r : ℝ)) =
        ∑ x ∈ C.centers, volume (Metric.ball x (r : ℝ)) := by
      simp [InnerProductSpace.volume_ball]
    _ = volume (⋃ x ∈ C.centers, Metric.ball x (r : ℝ)) := by
      symm
      exact measure_biUnion_finset C.smallBalls_pairwiseDisjoint
        (fun _ _ => measurableSet_ball)
    _ ≤ volume (Metric.thickening (r : ℝ) A) :=
      measure_mono C.iUnion_smallBalls_subset_thickening

theorem two_mul_lt_three_mul (r : ℝ≥0) (hr : 0 < r) :
    ((2 * r : ℝ≥0) : ℝ) < ((3 * r : ℝ≥0) : ℝ) := by
  exact_mod_cast (mul_lt_mul_of_pos_right (show (2 : ℝ≥0) < 3 by norm_num) hr)

/-- The closed `2r` cover is contained in an open `3r` cover. -/
theorem PackingCertificate.subset_iUnion_largeBalls
    {A : Set Space} {r : ℝ≥0} (C : PackingCertificate A r)
    (hr : 0 < r) :
    A ⊆ ⋃ x ∈ C.centers, Metric.ball x ((3 * r : ℝ≥0) : ℝ) := by
  intro y hy
  have hy' := C.cover.subset_iUnion_closedBall hy
  obtain ⟨x, hy'⟩ := Set.mem_iUnion.mp hy'
  obtain ⟨hx, hyx⟩ := Set.mem_iUnion.mp hy'
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
    Metric.closedBall_subset_ball (two_mul_lt_three_mul r hr) hyx⟩⟩

/-- The packed set is covered by the corresponding local frame-box pieces. -/
theorem PackingCertificate.subset_iUnion_largePieces
    (B : FrameBox) {A : Set Space} (hA : A ⊆ B.carrier)
    {r : ℝ≥0} (C : PackingCertificate A r) (hr : 0 < r) :
    A ⊆ ⋃ x ∈ C.centers,
      (B.carrier ∩ Metric.ball x ((3 * r : ℝ≥0) : ℝ)) := by
  intro y hy
  have hyCover := C.subset_iUnion_largeBalls hr hy
  obtain ⟨x, hyCover⟩ := Set.mem_iUnion.mp hyCover
  obtain ⟨hx, hyx⟩ := Set.mem_iUnion.mp hyCover
  exact Set.mem_iUnion.mpr ⟨x,
    Set.mem_iUnion.mpr ⟨hx, hA hy, hyx⟩⟩

/-- The large-ball cover and the proved frame-box local cap bound the packed
set by the number of actual centers. -/
theorem PackingCertificate.volume_le_card_smul_localBallCap
    (B : FrameBox) {A : Set Space} (hA : A ⊆ B.carrier)
    {r : ℝ≥0} (C : PackingCertificate A r) (hr : 0 < r) :
    volume A ≤ C.centers.card • localBallCap B (3 * r) := by
  calc
    volume A ≤ volume (⋃ x ∈ C.centers,
        (B.carrier ∩ Metric.ball x ((3 * r : ℝ≥0) : ℝ))) :=
      measure_mono (C.subset_iUnion_largePieces B hA hr)
    _ ≤ ∑ x ∈ C.centers,
        volume (B.carrier ∩ Metric.ball x ((3 * r : ℝ≥0) : ℝ)) :=
      measure_biUnion_finset_le C.centers _
    _ ≤ ∑ _x ∈ C.centers, localBallCap B (3 * r) := by
      apply Finset.sum_le_sum
      intro x hx
      simpa [localBallCap] using
        B.volume_carrier_inter_ball_le x (3 * r)
    _ = C.centers.card • localBallCap B (3 * r) := by simp

/-- Division-free covering growth for one concrete packing certificate. -/
theorem PackingCertificate.volume_mul_ballVolume_le_cap_mul_thickening
    (B : FrameBox) {A : Set Space} (hA : A ⊆ B.carrier)
    {r : ℝ≥0} (C : PackingCertificate A r) (hr : 0 < r) :
    volume A * volume (Metric.ball (0 : Space) (r : ℝ)) ≤
      localBallCap B (3 * r) * volume (Metric.thickening (r : ℝ) A) := by
  calc
    volume A * volume (Metric.ball (0 : Space) (r : ℝ)) ≤
        (C.centers.card • localBallCap B (3 * r)) *
          volume (Metric.ball (0 : Space) (r : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (C.volume_le_card_smul_localBallCap B hA hr) bot_le
    _ = localBallCap B (3 * r) *
        (C.centers.card • volume (Metric.ball (0 : Space) (r : ℝ))) := by
      simp only [nsmul_eq_mul]
      ac_rfl
    _ ≤ localBallCap B (3 * r) *
        volume (Metric.thickening (r : ℝ) A) :=
      mul_le_mul_of_nonneg_left C.card_smul_ballVolume_le_thickening bot_le

/-- Actual maximal-separated-set data and the resulting zero-division
covering-growth inequality.  Measurability is included to match the induced
shading application, although the outer-measure argument is valid for every
subset of the frame box. -/
theorem exists_packingCertificate_with_coveringGrowth
    (B : FrameBox) {A : Set Space} (_hAmeas : MeasurableSet A)
    (hA : A ⊆ B.carrier) (r : ℝ≥0) (hr : 0 < r) :
    ∃ C : PackingCertificate A r,
      C.centers.card • volume (Metric.ball (0 : Space) (r : ℝ)) ≤
          volume (Metric.thickening (r : ℝ) A) ∧
        volume A * volume (Metric.ball (0 : Space) (r : ℝ)) ≤
          localBallCap B (3 * r) * volume (Metric.thickening (r : ℝ) A) := by
  let C := Classical.choice (exists_packingCertificate B hA r hr)
  exact ⟨C, C.card_smul_ballVolume_le_thickening,
    C.volume_mul_ballVolume_le_cap_mul_thickening B hA hr⟩

end FrameBoxInducedCoveringGrowth

end

end Submission.Kakeya.ConvexGeometry
