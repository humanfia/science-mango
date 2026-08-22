import ChallengeDeps

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

/-!
# Unit segments and closed tubes

This module follows the geometric convention in Guth--Wang--Zahl: a
`δ`-tube is the closed `δ`-neighborhood of a unit line segment.
-/

/-- A parametrized line segment whose direction vector has norm one. -/
structure UnitSegment where
  base : Space
  direction : Space
  norm_direction : ‖direction‖ = 1

/-- The endpoint reached at parameter one. -/
def UnitSegment.endpoint (S : UnitSegment) : Space :=
  S.base + S.direction

/-- The geometric carrier of a unit segment. -/
def UnitSegment.carrier (S : UnitSegment) : Set Space :=
  segment ℝ S.base S.endpoint

/-- A unit segment is exactly the image of `[0,1]` under its standard
parametrization. -/
theorem UnitSegment.carrier_eq_image (S : UnitSegment) :
    S.carrier = (fun t : ℝ ↦ S.base + t • S.direction) '' Set.Icc 0 1 := by
  simpa [carrier, endpoint] using segment_eq_image' ℝ S.base S.endpoint

/-- Every parameter in `[0,1]` gives a point of the segment. -/
theorem UnitSegment.mem_carrier_of_mem_Icc
    (S : UnitSegment) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    S.base + t • S.direction ∈ S.carrier := by
  rw [S.carrier_eq_image]
  exact ⟨t, ht, rfl⟩

/-- The base point belongs to the segment. -/
theorem UnitSegment.base_mem_carrier (S : UnitSegment) : S.base ∈ S.carrier :=
  left_mem_segment ℝ S.base S.endpoint

/-- The endpoint belongs to the segment. -/
theorem UnitSegment.endpoint_mem_carrier (S : UnitSegment) : S.endpoint ∈ S.carrier :=
  right_mem_segment ℝ S.base S.endpoint

/-- The carrier of a unit segment is convex. -/
theorem UnitSegment.convex_carrier (S : UnitSegment) : Convex ℝ S.carrier :=
  convex_segment S.base S.endpoint

/-- The carrier of a unit segment is compact. -/
theorem UnitSegment.isCompact_carrier (S : UnitSegment) : IsCompact S.carrier := by
  rw [S.carrier_eq_image]
  exact isCompact_Icc.image
    (continuous_const.add (continuous_id.smul continuous_const))

/-- The two endpoints of a unit segment are distance one apart. -/
theorem UnitSegment.dist_base_endpoint (S : UnitSegment) : dist S.base S.endpoint = 1 := by
  simp [endpoint, dist_eq_norm, S.norm_direction]

/-- A closed `δ`-tube around a unit segment. -/
structure Tube (δ : ℝ≥0) where
  axis : UnitSegment

/-- The closed metric `δ`-neighborhood of the tube axis. -/
def Tube.carrier {δ : ℝ≥0} (T : Tube δ) : Set Space :=
  Metric.cthickening (δ : ℝ) T.axis.carrier

/-- A closed tube is convex. -/
theorem Tube.convex_carrier {δ : ℝ≥0} (T : Tube δ) : Convex ℝ T.carrier :=
  T.axis.convex_carrier.cthickening (δ : ℝ)

/-- A closed tube is compact. -/
theorem Tube.isCompact_carrier {δ : ℝ≥0} (T : Tube δ) : IsCompact T.carrier :=
  T.axis.isCompact_carrier.cthickening

/-- The tube contains its axis. -/
theorem Tube.axis_subset_carrier {δ : ℝ≥0} (T : Tube δ) :
    T.axis.carrier ⊆ T.carrier :=
  Metric.self_subset_cthickening _

/-- A tube regarded as a Mathlib convex body. -/
def Tube.body {δ : ℝ≥0} (T : Tube δ) : ConvexBody Space where
  carrier := T.carrier
  convex' := T.convex_carrier
  isCompact' := T.isCompact_carrier
  nonempty' := ⟨T.axis.base, T.axis_subset_carrier T.axis.base_mem_carrier⟩

@[simp]
theorem Tube.coe_body {δ : ℝ≥0} (T : Tube δ) : (T.body : Set Space) = T.carrier :=
  rfl

/-- Every closed tube has finite Euclidean volume. -/
theorem Tube.volume_lt_top {δ : ℝ≥0} (T : Tube δ) : volume T.carrier < ∞ :=
  T.isCompact_carrier.measure_lt_top

/-- A tube of positive radius has positive Euclidean volume. -/
theorem Tube.volume_pos {δ : ℝ≥0} (T : Tube δ) (hδ : 0 < δ) : 0 < volume T.carrier := by
  refine (Metric.measure_closedBall_pos volume T.axis.base (NNReal.coe_pos.2 hδ)).trans_le ?_
  exact measure_mono (Metric.closedBall_subset_cthickening T.axis.base_mem_carrier (δ : ℝ))

end Submission.Kakeya.ConvexGeometry
