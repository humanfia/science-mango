import ChallengeDeps

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

/-!
# Finite families of convex bodies

Families are indexed rather than represented by a `Finset (Set Space)`.  This
preserves repetitions, which are meaningful in multiplicity and refinement
arguments.  Finiteness is supplied by a `Fintype` instance when sums or finite
unions are formed.
-/

/-- A family of convex bodies, indexed so repetitions remain visible. -/
abbrev ConvexFamily (ι : Type*) := ι → ConvexBody Space

/-- The union of all members of a convex family. -/
def familyUnion {ι : Type*} (F : ConvexFamily ι) : Set Space :=
  ⋃ i, (F i : Set Space)

/-- The sum of the volumes of all members of a finite convex family. -/
noncomputable def familyVolume {ι : Type*} [Fintype ι] (F : ConvexFamily ι) : ℝ≥0∞ :=
  ∑ i, volume (F i : Set Space)

/-- The indices of family members contained in a convex body. -/
noncomputable def containedIndices {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ (F i : Set Space) ⊆ (K : Set Space)

/-- The volume concentration of a convex family inside a convex body.

The numerator counts repetitions in the indexed family. -/
noncomputable def concentration {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) : ℝ≥0∞ :=
  (∑ i ∈ containedIndices F K, volume (F i : Set Space)) / volume (K : Set Space)

/-- Supremal volume concentration over compact, nonempty convex bodies.

This is an `iSup`: the API does not assert that a maximizing body exists. -/
noncomputable def maximalConcentration {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) : ℝ≥0∞ :=
  ⨆ K : ConvexBody Space, concentration F K

/-- A finite union of compact family members is compact. -/
theorem familyUnion_isCompact {ι : Type*} [Fintype ι] (F : ConvexFamily ι) :
    IsCompact (familyUnion F) :=
  isCompact_iUnion fun i ↦ (F i).isCompact

/-- The union of a finite convex family is measurable. -/
theorem familyUnion_measurableSet {ι : Type*} [Fintype ι] (F : ConvexFamily ι) :
    MeasurableSet (familyUnion F) :=
  (familyUnion_isCompact F).measurableSet

/-- The volume of a finite union is at most the sum of member volumes. -/
theorem volume_familyUnion_le {ι : Type*} [Fintype ι] (F : ConvexFamily ι) :
    volume (familyUnion F) ≤ familyVolume F :=
  measure_iUnion_fintype_le volume fun i ↦ (F i : Set Space)

/-- The summed volume of a finite family of compact bodies is finite. -/
theorem familyVolume_lt_top {ι : Type*} [Fintype ι] (F : ConvexFamily ι) :
    familyVolume F < ∞ := by
  rw [familyVolume]
  exact ENNReal.sum_lt_top.mpr fun i _ ↦ (F i).isCompact.measure_lt_top

/-- The summed family volume is not infinite. -/
theorem familyVolume_ne_top {ι : Type*} [Fintype ι] (F : ConvexFamily ι) :
    familyVolume F ≠ ∞ :=
  (familyVolume_lt_top F).ne

/-- Every particular concentration is bounded by the supremal concentration. -/
theorem concentration_le_maximalConcentration {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) :
    concentration F K ≤ maximalConcentration F :=
  le_iSup (concentration F) K

end Submission.Kakeya.ConvexGeometry
