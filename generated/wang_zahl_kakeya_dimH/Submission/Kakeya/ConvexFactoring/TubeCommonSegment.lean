import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure

open Set
open scoped NNReal

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Tube containment from a common unit segment

This module proves the geometric containment needed before adjacent tube-cover
levels can be assembled into a hierarchy.  If a unit segment lies in both a
child `r`-tube and a parent tube, then the child is contained in the closed
`4r`-neighborhood of the parent.  A common fine tube supplies such a segment by
using its axis.

The frequently quoted sharper constant `2r` does not follow from the common
unit-segment hypothesis, even when `r` is at most the parent radius.  For
example, in a coordinate plane take the common segment to be horizontal, let
`r = 1/10`, give the child direction `(99/101, 20/101)` with parameter interval
`[-13/25, 12/25]`, and take the parent to be the common segment translated
upward by `1/2`, with radius `1/2`.  The common segment lies in both tubes, but
a point on the lower edge of the child lies outside the `2r`-neighborhood of
the parent.  The factor four below is a safe proved replacement.

This remains geometric infrastructure.  It does not construct a
`CoarseTubePartition` or a multiscale tube hierarchy.
-/

namespace UnitSegment

/-- Standard affine parameterization of a unit segment. -/
def point (S : UnitSegment) (t : ℝ) : Space :=
  S.base + t • S.direction

@[simp] theorem point_zero (S : UnitSegment) : S.point 0 = S.base := by
  simp [point]

@[simp] theorem point_one (S : UnitSegment) : S.point 1 = S.endpoint := by
  simp [point, endpoint]

/-- A parameter in `[0,1]` gives a point of the segment carrier. -/
theorem point_mem_carrier (S : UnitSegment) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    S.point t ∈ S.carrier :=
  S.mem_carrier_of_mem_Icc ht

/-- Distance along the standard unit-speed parameterization. -/
theorem dist_point_point (S : UnitSegment) (s t : ℝ) :
    dist (S.point s) (S.point t) = |s - t| := by
  rw [dist_eq_norm]
  simp only [point, add_sub_add_left_eq_sub, ← sub_smul]
  rw [norm_smul, S.norm_direction, mul_one, Real.norm_eq_abs]

end UnitSegment

namespace Tube

/-- A point of a common unit segment admits a nearby parameter point on the
tube axis. -/
theorem exists_axis_parameter_dist_le_of_commonSegment
    {r : NNReal} (T : Tube r) (L : UnitSegment)
    (hL : L.carrier ⊆ T.carrier) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      dist (L.point t) (T.axis.point s) ≤ (r : ℝ) := by
  have hx : L.point t ∈ T.carrier := hL (L.point_mem_carrier ht)
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (r : ℝ) by positivity)] at hx
  simp only [mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hyAxis, hdist⟩ := hx
  rw [T.axis.carrier_eq_image] at hyAxis
  obtain ⟨s, hs, rfl⟩ := hyAxis
  exact ⟨s, hs, hdist⟩

/-- If a unit segment lies in an `r`-tube, then the tube axis lies in the
`3r`-neighborhood of that segment. -/
theorem axis_subset_three_mul_cthickening_of_commonSegment
    {r : NNReal} (T : Tube r) (L : UnitSegment)
    (hL : L.carrier ⊆ T.carrier) :
    T.axis.carrier ⊆ Metric.cthickening (3 * (r : ℝ)) L.carrier := by
  obtain ⟨s0, hs0, hdist0⟩ :=
    T.exists_axis_parameter_dist_le_of_commonSegment L hL
      (t := 0) (by norm_num)
  obtain ⟨s1, hs1, hdist1⟩ :=
    T.exists_axis_parameter_dist_le_of_commonSegment L hL
      (t := 1) (by norm_num)
  have hsepRaw : (1 : ℝ) ≤ (r : ℝ) + |s0 - s1| + (r : ℝ) := by
    calc
      (1 : ℝ) = dist (L.point 0) (L.point 1) := by
        rw [L.dist_point_point]
        norm_num
      _ ≤ dist (L.point 0) (T.axis.point s0) +
            dist (T.axis.point s0) (T.axis.point s1) +
            dist (T.axis.point s1) (L.point 1) := dist_triangle4 _ _ _ _
      _ ≤ (r : ℝ) + |s0 - s1| + (r : ℝ) := by
        rw [T.axis.dist_point_point]
        exact add_le_add (add_le_add hdist0 le_rfl)
          (by simpa [dist_comm] using hdist1)
  have hsep : (1 : ℝ) - 2 * (r : ℝ) ≤ |s0 - s1| := by linarith
  have hconvex : Convex ℝ (Metric.cthickening (3 * (r : ℝ)) L.carrier) :=
    L.convex_carrier.cthickening _
  rcases le_total s0 s1 with hs01 | hs10
  · have habs : |s0 - s1| = s1 - s0 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hs01)]
      ring
    have hs0Upper : s0 ≤ 2 * (r : ℝ) := by
      rw [habs] at hsep
      linarith [hs1.2]
    have hs1Lower : (1 : ℝ) - s1 ≤ 2 * (r : ℝ) := by
      rw [habs] at hsep
      linarith [hs0.1]
    have hbaseDist : dist T.axis.base L.base ≤ 3 * (r : ℝ) := by
      calc
        dist T.axis.base L.base ≤ dist T.axis.base (T.axis.point s0) +
            dist (T.axis.point s0) L.base := dist_triangle _ _ _
        _ ≤ s0 + (r : ℝ) := by
          apply add_le_add
          · rw [← T.axis.point_zero, T.axis.dist_point_point]
            simp [abs_of_nonneg hs0.1]
          · simpa [L.point_zero, dist_comm] using hdist0
        _ ≤ 3 * (r : ℝ) := by linarith
    have hendDist : dist T.axis.endpoint L.endpoint ≤ 3 * (r : ℝ) := by
      calc
        dist T.axis.endpoint L.endpoint ≤ dist T.axis.endpoint (T.axis.point s1) +
            dist (T.axis.point s1) L.endpoint := dist_triangle _ _ _
        _ ≤ (1 - s1) + (r : ℝ) := by
          apply add_le_add
          · rw [← T.axis.point_one, T.axis.dist_point_point]
            simp [abs_of_nonneg (sub_nonneg.mpr hs1.2)]
          · simpa [L.point_one, dist_comm] using hdist1
        _ ≤ 3 * (r : ℝ) := by linarith
    have hbaseMem : T.axis.base ∈
        Metric.cthickening (3 * (r : ℝ)) L.carrier :=
      Metric.closedBall_subset_cthickening L.base_mem_carrier _
        (by simpa [Metric.mem_closedBall, dist_comm] using hbaseDist)
    have hendMem : T.axis.endpoint ∈
        Metric.cthickening (3 * (r : ℝ)) L.carrier :=
      Metric.closedBall_subset_cthickening L.endpoint_mem_carrier _
        (by simpa [Metric.mem_closedBall, dist_comm] using hendDist)
    simpa [UnitSegment.carrier] using hconvex.segment_subset hbaseMem hendMem
  · have habs : |s0 - s1| = s0 - s1 :=
      abs_of_nonneg (sub_nonneg.mpr hs10)
    have hs1Upper : s1 ≤ 2 * (r : ℝ) := by
      rw [habs] at hsep
      linarith [hs0.2]
    have hs0Lower : (1 : ℝ) - s0 ≤ 2 * (r : ℝ) := by
      rw [habs] at hsep
      linarith [hs1.1]
    have hbaseDist : dist T.axis.base L.endpoint ≤ 3 * (r : ℝ) := by
      calc
        dist T.axis.base L.endpoint ≤ dist T.axis.base (T.axis.point s1) +
            dist (T.axis.point s1) L.endpoint := dist_triangle _ _ _
        _ ≤ s1 + (r : ℝ) := by
          apply add_le_add
          · rw [← T.axis.point_zero, T.axis.dist_point_point]
            simp [abs_of_nonneg hs1.1]
          · simpa [L.point_one, dist_comm] using hdist1
        _ ≤ 3 * (r : ℝ) := by linarith
    have hendDist : dist T.axis.endpoint L.base ≤ 3 * (r : ℝ) := by
      calc
        dist T.axis.endpoint L.base ≤ dist T.axis.endpoint (T.axis.point s0) +
            dist (T.axis.point s0) L.base := dist_triangle _ _ _
        _ ≤ (1 - s0) + (r : ℝ) := by
          apply add_le_add
          · rw [← T.axis.point_one, T.axis.dist_point_point]
            simp [abs_of_nonneg (sub_nonneg.mpr hs0.2)]
          · simpa [L.point_zero, dist_comm] using hdist0
        _ ≤ 3 * (r : ℝ) := by linarith
    have hbaseMem : T.axis.base ∈
        Metric.cthickening (3 * (r : ℝ)) L.carrier :=
      Metric.closedBall_subset_cthickening L.endpoint_mem_carrier _
        (by simpa [Metric.mem_closedBall, dist_comm] using hbaseDist)
    have hendMem : T.axis.endpoint ∈
        Metric.cthickening (3 * (r : ℝ)) L.carrier :=
      Metric.closedBall_subset_cthickening L.base_mem_carrier _
        (by simpa [Metric.mem_closedBall, dist_comm] using hendDist)
    simpa [UnitSegment.carrier] using hconvex.segment_subset hbaseMem hendMem

/-- A common unit-segment witness puts the entire child tube in the `4r` closed
neighborhood of the parent.  No comparison between the child radius `r` and
the parent radius `R` is needed once the common segment lies in both carriers. -/
theorem carrier_subset_four_mul_cthickening_of_commonSegment
    {r R : NNReal} (child : Tube r) (parent : Tube R) (L : UnitSegment)
    (hChild : L.carrier ⊆ child.carrier)
    (hParent : L.carrier ⊆ parent.carrier) :
    child.carrier ⊆
      Metric.cthickening (4 * (r : ℝ)) parent.carrier := by
  have hAxis := child.axis_subset_three_mul_cthickening_of_commonSegment L hChild
  have hBufferedAxis :=
    Metric.cthickening_subset_of_subset (r : ℝ) hAxis
  rw [cthickening_cthickening (by positivity) (by positivity)] at hBufferedAxis
  have hWitnessToParent :=
    Metric.cthickening_subset_of_subset (4 * (r : ℝ)) hParent
  have hBufferedAxis' : child.carrier ⊆
      Metric.cthickening (4 * (r : ℝ)) L.carrier := by
    rw [Tube.carrier]
    have hr : (r : ℝ) + 3 * (r : ℝ) = 4 * (r : ℝ) := by ring
    simpa only [hr] using hBufferedAxis
  exact hBufferedAxis'.trans hWitnessToParent

/-- The common segment can be supplied as the axis of a fine tube contained in
both the child and the parent. -/
theorem carrier_subset_four_mul_cthickening_of_commonFineTube
    {δ r R : NNReal} (fine : Tube δ) (child : Tube r) (parent : Tube R)
    (hFineChild : fine.carrier ⊆ child.carrier)
    (hFineParent : fine.carrier ⊆ parent.carrier) :
    child.carrier ⊆
      Metric.cthickening (4 * (r : ℝ)) parent.carrier :=
  child.carrier_subset_four_mul_cthickening_of_commonSegment parent fine.axis
    (fine.axis_subset_carrier.trans hFineChild)
    (fine.axis_subset_carrier.trans hFineParent)

/-- Recursive-buffer form of common-fine-tube containment.  The child may
already carry a buffer `q`; adding `4r + q` to the raw parent produces exact
carrier containment and records the effective radii in the result types. -/
theorem buffered_carrier_subset_of_commonFineTube
    {δ r R : NNReal} (fine : Tube δ) (child : Tube r) (parent : Tube R)
    (q : NNReal)
    (hFineChild : fine.carrier ⊆ child.carrier)
    (hFineParent : fine.carrier ⊆ parent.carrier) :
    (child.buffer q).carrier ⊆
      (parent.buffer (4 * r + q)).carrier := by
  apply buffer_subset_buffer_add_of_subset_cthickening
    (c := 4 * r) (q := q)
  simpa [NNReal.coe_mul] using
    carrier_subset_four_mul_cthickening_of_commonFineTube
      fine child parent hFineChild hFineParent

end Tube

end

end Submission.Kakeya.ConvexGeometry
