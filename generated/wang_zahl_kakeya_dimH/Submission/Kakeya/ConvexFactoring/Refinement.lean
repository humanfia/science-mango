import Submission.Kakeya.ConvexGeometry.Shading

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

/-!
# Refinements of indexed shadings

This module records the monotonicity facts used when a shaded convex family is
replaced by a subfamily and each of its shaded pieces is made smaller.
-/

/-- A subfamily/subshading refinement on the original index type. -/
structure IndexedShadingRefinement {ι : Type*} [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F) where
  indices : Finset ι
  shading : Shading F
  carrier_subset : ∀ i, shading.carrier i ⊆ Y.carrier i
  carrier_eq_empty_of_not_mem : ∀ i, i ∉ indices → shading.carrier i = ∅

namespace IndexedShadingRefinement

/-- Restrict a shading to a finite set of indices. -/
def restrictTo {ι : Type*} [DecidableEq ι] {F : ConvexFamily ι}
    (Y : Shading F) (s : Finset ι) : IndexedShadingRefinement Y where
  indices := s
  shading :=
    { carrier := fun i ↦ if i ∈ s then Y.carrier i else ∅
      measurable_carrier := fun i ↦ by
        split_ifs <;> simp_all [Y.measurable_carrier]
      carrier_subset := fun i ↦ by
        split_ifs
        · exact Y.carrier_subset i
        · exact Set.empty_subset _ }
  carrier_subset := fun i ↦ by
    change (if i ∈ s then Y.carrier i else ∅) ⊆ Y.carrier i
    split_ifs
    · exact fun _ hx ↦ hx
    · exact Set.empty_subset _
  carrier_eq_empty_of_not_mem := fun i hi ↦ by simp [hi]

@[simp] theorem restrictTo_carrier {ι : Type*} [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F) (s : Finset ι) (i : ι) :
    (restrictTo Y s).shading.carrier i = if i ∈ s then Y.carrier i else ∅ :=
  rfl

/-- Refining each shaded piece can only shrink their union. -/
theorem shadedUnion_subset {ι : Type*} [DecidableEq ι]
    {F : ConvexFamily ι} {Y : Shading F} (R : IndexedShadingRefinement Y) :
    R.shading.shadedUnion ⊆ Y.shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i, R.carrier_subset i hxi⟩

/-- Refining a finite shading cannot increase its total shaded mass. -/
theorem shadingMass_le {ι : Type*} [DecidableEq ι] [Fintype ι]
    {F : ConvexFamily ι} {Y : Shading F} (R : IndexedShadingRefinement Y) :
    R.shading.shadingMass ≤ Y.shadingMass := by
  unfold Shading.shadingMass
  exact Finset.sum_le_sum fun i _ ↦ measure_mono (R.carrier_subset i)

/-- Refining a finite shading cannot increase pointwise multiplicity. -/
theorem pointMultiplicity_le {ι : Type*} [DecidableEq ι] [Fintype ι]
    {F : ConvexFamily ι} {Y : Shading F} (R : IndexedShadingRefinement Y)
    (x : Space) :
    R.shading.pointMultiplicity x ≤ Y.pointMultiplicity x := by
  classical
  unfold Shading.pointMultiplicity
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, R.carrier_subset i hi.2⟩

/-- Multiplicity at a point, counting only indices in a prescribed finite set. -/
noncomputable def restrictedPointMultiplicity {ι : Type*} [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F) (s : Finset ι) (x : Space) : ℕ := by
  classical
  exact (s.filter fun i ↦ x ∈ Y.carrier i).card

/-- Restricting the shading realizes the corresponding restricted
point-multiplicity exactly. -/
theorem pointMultiplicity_restrictTo {ι : Type*} [DecidableEq ι] [Fintype ι]
    {F : ConvexFamily ι} (Y : Shading F) (s : Finset ι) (x : Space) :
    (restrictTo Y s).shading.pointMultiplicity x =
      restrictedPointMultiplicity Y s x := by
  classical
  unfold Shading.pointMultiplicity
  apply congrArg Finset.card
  ext i
  simp [restrictTo]

end IndexedShadingRefinement

end Submission.Kakeya.ConvexFactoring
