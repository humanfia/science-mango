import Submission.Kakeya.ConvexGeometry.Family

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

/-!
# Shadings, density, and multiplicity

A shading is a measurable subset of each member of a convex family.  The
definitions below formalize the quantities `U`, `λ`, and `μ` from Section 2.1
of Guth--Wang--Zahl.
-/

/-- A measurable shading assigns to every family member a measurable subset
of that member. -/
structure Shading {ι : Type*} (F : ConvexFamily ι) where
  carrier : ι → Set Space
  measurable_carrier : ∀ i, MeasurableSet (carrier i)
  carrier_subset : ∀ i, carrier i ⊆ (F i : Set Space)

variable {ι : Type*} {F : ConvexFamily ι} (Y : Shading F)

/-- The union of all shaded pieces. -/
def Shading.shadedUnion : Set Space :=
  ⋃ i, Y.carrier i

/-- Total shaded mass, with overlaps counted once for every family index. -/
noncomputable def Shading.shadingMass [Fintype ι] : ℝ≥0∞ :=
  ∑ i, volume (Y.carrier i)

/-- The average fraction `λ` of the summed family volume that is shaded. -/
noncomputable def Shading.shadingDensity [Fintype ι] : ℝ≥0∞ :=
  Y.shadingMass / familyVolume F

/-- The averaged multiplicity `μ`: shaded mass divided by union volume. -/
noncomputable def Shading.averageMultiplicity [Fintype ι] : ℝ≥0∞ :=
  Y.shadingMass / volume Y.shadedUnion

/-- The number of shaded family members containing a point. -/
noncomputable def Shading.pointMultiplicity [Fintype ι] (x : Space) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ x ∈ Y.carrier i).card

/-- The shaded union is contained in the union of the underlying bodies. -/
theorem Shading.shadedUnion_subset_familyUnion : Y.shadedUnion ⊆ familyUnion F := by
  intro x hx
  change x ∈ ⋃ i, Y.carrier i at hx
  change x ∈ ⋃ i, (F i : Set Space)
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i, Y.carrier_subset i hxi⟩

/-- A finite union of measurable shaded pieces is measurable. -/
theorem Shading.shadedUnion_measurableSet [Fintype ι] : MeasurableSet Y.shadedUnion :=
  MeasurableSet.iUnion fun i ↦ Y.measurable_carrier i

/-- Total shaded mass is at most the summed volume of the family. -/
theorem Shading.shadingMass_le_familyVolume [Fintype ι] : Y.shadingMass ≤ familyVolume F := by
  unfold Shading.shadingMass familyVolume
  exact Finset.sum_le_sum fun i _ ↦ measure_mono (Y.carrier_subset i)

/-- Total shaded mass is finite. -/
theorem Shading.shadingMass_lt_top [Fintype ι] : Y.shadingMass < ∞ :=
  Y.shadingMass_le_familyVolume.trans_lt (familyVolume_lt_top F)

/-- Shading density is at most one, including the zero-volume case. -/
theorem Shading.shadingDensity_le_one [Fintype ι] : Y.shadingDensity ≤ 1 := by
  unfold Shading.shadingDensity
  rw [ENNReal.div_le_iff_le_mul (by simp) (Or.inl (familyVolume_ne_top F))]
  simpa using Y.shadingMass_le_familyVolume

/-- Pointwise multiplicity is positive exactly on the shaded union. -/
theorem Shading.pointMultiplicity_pos_iff_mem_shadedUnion [Fintype ι] (x : Space) :
    0 < Y.pointMultiplicity x ↔ x ∈ Y.shadedUnion := by
  classical
  unfold Shading.pointMultiplicity Shading.shadedUnion
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and, Set.mem_iUnion]

/-- Pointwise multiplicity is bounded by the size of the index type. -/
theorem Shading.pointMultiplicity_le_card [Fintype ι] (x : Space) :
    Y.pointMultiplicity x ≤ Fintype.card ι := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The natural-valued multiplicity is the sum of membership indicators. -/
theorem Shading.pointMultiplicity_cast_eq_sum_indicator [Fintype ι] (x : Space) :
    (Y.pointMultiplicity x : ℝ≥0∞) =
      ∑ i, (Y.carrier i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  classical
  simp [Shading.pointMultiplicity, Set.indicator_apply]

/-- The first moment of pointwise multiplicity equals total shaded mass. -/
theorem Shading.lintegral_pointMultiplicity [Fintype ι] :
    ∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ∂volume = Y.shadingMass := by
  simp_rw [Y.pointMultiplicity_cast_eq_sum_indicator]
  unfold Shading.shadingMass
  rw [lintegral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    exact lintegral_indicator_one (Y.measurable_carrier i)
  · intro i _
    exact measurable_const.indicator (Y.measurable_carrier i)

end Submission.Kakeya.ConvexGeometry
