import Submission.Kakeya.ConvexFactoring.L2Union

/-!
# Finite-family pointwise multiplicity pigeonholing

This file supplies the constant-multiplicity decomposition used before the
geometric refinements in the Wang--Zahl argument. It treats all multiplicity
levels, including level zero, and uses a division-free finite pigeonhole
conclusion.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι : Type*} {F : ConvexFamily ι}

/-- Restrict every shaded piece to the same measurable set. -/
def Shading.restrictSet (Y : Shading F) (Ω : Set Space)
    (hΩ : MeasurableSet Ω) : Shading F where
  carrier i := Y.carrier i ∩ Ω
  measurable_carrier i := (Y.measurable_carrier i).inter hΩ
  carrier_subset i := (inter_subset_left : Y.carrier i ∩ Ω ⊆ Y.carrier i).trans
    (Y.carrier_subset i)

@[simp]
theorem Shading.restrictSet_carrier (Y : Shading F) (Ω : Set Space)
    (hΩ : MeasurableSet Ω) (i : ι) :
    (Y.restrictSet Ω hΩ).carrier i = Y.carrier i ∩ Ω :=
  rfl

/-- Restricting every piece restricts the shaded union by the same set. -/
theorem Shading.restrictSet_shadedUnion (Y : Shading F) (Ω : Set Space)
    (hΩ : MeasurableSet Ω) :
    (Y.restrictSet Ω hΩ).shadedUnion = Y.shadedUnion ∩ Ω := by
  ext x
  constructor
  · intro hx
    change x ∈ ⋃ i, Y.carrier i ∩ Ω at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact ⟨Set.mem_iUnion.mpr ⟨i, hxi.1⟩, hxi.2⟩
  · rintro ⟨hxY, hxΩ⟩
    change x ∈ ⋃ i, Y.carrier i at hxY
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxY
    change x ∈ ⋃ i, Y.carrier i ∩ Ω
    exact Set.mem_iUnion.mpr ⟨i, hxi, hxΩ⟩

variable [Fintype ι]

/-- Pointwise multiplicity after a common set restriction. -/
theorem Shading.pointMultiplicity_restrictSet (Y : Shading F)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (x : Space) :
    (Y.restrictSet Ω hΩ).pointMultiplicity x =
      if x ∈ Ω then Y.pointMultiplicity x else 0 := by
  classical
  unfold Shading.pointMultiplicity
  by_cases hx : x ∈ Ω <;> simp [Shading.restrictSet, hx]

/-- Points of the shaded union having exactly multiplicity `n`. -/
def multiplicitySlice (Y : Shading F) (n : ℕ) : Set Space :=
  Y.shadedUnion ∩ {x | Y.pointMultiplicity x = n}

/-- Every multiplicity slice is measurable. -/
theorem measurableSet_multiplicitySlice (Y : Shading F) (n : ℕ) :
    MeasurableSet (multiplicitySlice Y n) := by
  have heq :
      {x | Y.pointMultiplicity x = n} =
        (fun x => (Y.pointMultiplicity x : ℝ≥0∞)) ⁻¹' {(n : ℝ≥0∞)} := by
    ext x
    simp
  rw [multiplicitySlice, heq]
  exact Y.shadedUnion_measurableSet.inter
    ((measurable_pointMultiplicity Y) (measurableSet_singleton _))

/-- Distinct multiplicity slices are disjoint. -/
theorem multiplicitySlice_disjoint (Y : Shading F) {m n : ℕ}
    (hmn : m ≠ n) :
    Disjoint (multiplicitySlice Y m) (multiplicitySlice Y n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  exact hmn (hxm.2.symm.trans hxn.2)

/-- The levels `0, ..., card ι` exactly cover the shaded union. -/
theorem Shading.shadedUnion_eq_iUnion_multiplicitySlice (Y : Shading F) :
    Y.shadedUnion =
      ⋃ n ∈ Finset.range (Fintype.card ι + 1), multiplicitySlice Y n := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.mpr ⟨Y.pointMultiplicity x, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_, hx, rfl⟩
    exact Nat.lt_succ_of_le (Y.pointMultiplicity_le_card x)
  · intro hx
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hn, hx⟩ := Set.mem_iUnion.mp hx
    exact hx.1

/-- The multiplicity slices in the finite level range are pairwise disjoint. -/
theorem pairwiseDisjoint_multiplicitySlice (Y : Shading F) :
    Set.PairwiseDisjoint
      (↑(Finset.range (Fintype.card ι + 1)) : Set ℕ)
      (multiplicitySlice Y) := by
  intro m hm n hn hmn
  exact multiplicitySlice_disjoint Y hmn

/-- The shaded union measure is the sum of the measures of all finite
multiplicity slices. -/
theorem Shading.volume_shadedUnion_eq_sum_multiplicitySlice (Y : Shading F) :
    volume Y.shadedUnion =
      ∑ n ∈ Finset.range (Fintype.card ι + 1),
        volume (multiplicitySlice Y n) := by
  rw [Y.shadedUnion_eq_iUnion_multiplicitySlice]
  exact measure_biUnion_finset (pairwiseDisjoint_multiplicitySlice Y)
    (fun n hn => measurableSet_multiplicitySlice Y n)

/-- Pointwise, multiplicity is the finite sum of its constant values on the
multiplicity slices. -/
theorem Shading.pointMultiplicity_cast_eq_sum_multiplicitySlice_indicator
    (Y : Shading F) (x : Space) :
    (Y.pointMultiplicity x : ℝ≥0∞) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1),
        (multiplicitySlice Y n).indicator (fun _ => (n : ℝ≥0∞)) x := by
  classical
  by_cases hx : x ∈ Y.shadedUnion
  · have hm : Y.pointMultiplicity x ∈ Finset.range (Fintype.card ι + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Y.pointMultiplicity_le_card x))
    rw [Finset.sum_eq_single (Y.pointMultiplicity x)]
    · simp [multiplicitySlice, hx]
    · intro n hn hne
      have hxnot : x ∉ multiplicitySlice Y n := by
        intro hxn
        exact hne hxn.2.symm
      simp [hxnot]
    · exact fun hnot => (hnot hm).elim
  · have hmzero : Y.pointMultiplicity x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hx ((Y.pointMultiplicity_pos_iff_mem_shadedUnion x).mp hpos)
    simp [multiplicitySlice, hx, hmzero]

/-- Exact first-moment decomposition into constant-multiplicity slices. -/
theorem Shading.shadingMass_eq_sum_multiplicitySlice (Y : Shading F) :
    Y.shadingMass =
      ∑ n ∈ Finset.range (Fintype.card ι + 1),
        (n : ℝ≥0∞) * volume (multiplicitySlice Y n) := by
  rw [← Y.lintegral_pointMultiplicity]
  calc
    (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ∂volume) =
        ∫⁻ x, ∑ n ∈ Finset.range (Fintype.card ι + 1),
          (multiplicitySlice Y n).indicator (fun _ => (n : ℝ≥0∞)) x ∂volume := by
      congr 1
      funext x
      exact Y.pointMultiplicity_cast_eq_sum_multiplicitySlice_indicator x
    _ = ∑ n ∈ Finset.range (Fintype.card ι + 1),
          ∫⁻ x, (multiplicitySlice Y n).indicator
            (fun _ => (n : ℝ≥0∞)) x ∂volume := by
      apply lintegral_finsetSum
      intro n hn
      exact measurable_const.indicator (measurableSet_multiplicitySlice Y n)
    _ = ∑ n ∈ Finset.range (Fintype.card ι + 1),
          (n : ℝ≥0∞) * volume (multiplicitySlice Y n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [lintegral_indicator (measurableSet_multiplicitySlice Y n),
        setLIntegral_const]

/-- The shading obtained by restricting every piece to one multiplicity
slice. -/
def Shading.restrictMultiplicitySlice (Y : Shading F) (n : ℕ) : Shading F :=
  Y.restrictSet (multiplicitySlice Y n) (measurableSet_multiplicitySlice Y n)

@[simp]
theorem Shading.restrictMultiplicitySlice_carrier (Y : Shading F)
    (n : ℕ) (i : ι) :
    (Y.restrictMultiplicitySlice n).carrier i =
      Y.carrier i ∩ multiplicitySlice Y n :=
  rfl

/-- The shaded union of the slice restriction is exactly that slice. -/
theorem Shading.restrictMultiplicitySlice_shadedUnion (Y : Shading F)
    (n : ℕ) :
    (Y.restrictMultiplicitySlice n).shadedUnion = multiplicitySlice Y n := by
  rw [Shading.restrictMultiplicitySlice, Shading.restrictSet_shadedUnion]
  exact Set.inter_eq_right.mpr inter_subset_left

/-- The restricted multiplicity is `n` on the selected slice and zero off it. -/
theorem Shading.pointMultiplicity_restrictMultiplicitySlice
    (Y : Shading F) (n : ℕ) (x : Space) :
    (Y.restrictMultiplicitySlice n).pointMultiplicity x =
      if x ∈ multiplicitySlice Y n then n else 0 := by
  rw [Shading.restrictMultiplicitySlice,
    Shading.pointMultiplicity_restrictSet]
  by_cases hx : x ∈ multiplicitySlice Y n
  · simp only [if_pos hx]
    exact hx.2
  · simp only [if_neg hx]

/-- Consequently the restricted point multiplicity is constant on its shaded
union. -/
theorem Shading.pointMultiplicity_restrictMultiplicitySlice_eq
    (Y : Shading F) (n : ℕ) (x : Space)
    (hx : x ∈ (Y.restrictMultiplicitySlice n).shadedUnion) :
    (Y.restrictMultiplicitySlice n).pointMultiplicity x = n := by
  rw [Y.restrictMultiplicitySlice_shadedUnion] at hx
  rw [Y.pointMultiplicity_restrictMultiplicitySlice, if_pos hx]

/-- The mass of the restriction is exactly multiplicity times slice volume. -/
theorem Shading.shadingMass_restrictMultiplicitySlice (Y : Shading F)
    (n : ℕ) :
    (Y.restrictMultiplicitySlice n).shadingMass =
      (n : ℝ≥0∞) * volume (multiplicitySlice Y n) := by
  rw [← (Y.restrictMultiplicitySlice n).lintegral_pointMultiplicity]
  calc
    (∫⁻ x, ((Y.restrictMultiplicitySlice n).pointMultiplicity x : ℝ≥0∞)
        ∂volume) =
        ∫⁻ x, (multiplicitySlice Y n).indicator
          (fun _ => (n : ℝ≥0∞)) x ∂volume := by
      congr 1
      funext x
      rw [Y.pointMultiplicity_restrictMultiplicitySlice]
      by_cases hx : x ∈ multiplicitySlice Y n
      · simp [hx]
      · simp [hx]
    _ = (n : ℝ≥0∞) * volume (multiplicitySlice Y n) := by
      rw [lintegral_indicator (measurableSet_multiplicitySlice Y n),
        setLIntegral_const]

/-- Some actual multiplicity level retains at least a `1 / (card ι + 1)`
fraction of the total shaded mass, stated without division. The result also
records the constant-multiplicity property of the selected restriction. -/
theorem Shading.exists_restrictMultiplicitySlice_with_large_mass
    (Y : Shading F) :
    ∃ n ∈ Finset.range (Fintype.card ι + 1),
      Y.shadingMass ≤
          (Fintype.card ι + 1) •
            (Y.restrictMultiplicitySlice n).shadingMass ∧
        ∀ x ∈ (Y.restrictMultiplicitySlice n).shadedUnion,
          (Y.restrictMultiplicitySlice n).pointMultiplicity x = n := by
  classical
  have hlevels : (Finset.range (Fintype.card ι + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  let w : ℕ → ℝ≥0∞ := fun n =>
    (n : ℝ≥0∞) * volume (multiplicitySlice Y n)
  obtain ⟨n, hn, hmax⟩ :=
    Finset.exists_max_image (Finset.range (Fintype.card ι + 1)) w hlevels
  refine ⟨n, hn, ?_, ?_⟩
  · calc
      Y.shadingMass = ∑ k ∈ Finset.range (Fintype.card ι + 1), w k := by
        simpa [w] using Y.shadingMass_eq_sum_multiplicitySlice
      _ ≤ (Finset.range (Fintype.card ι + 1)).card • w n :=
        Finset.sum_le_card_nsmul _ w (w n) (fun k hk => hmax k hk)
      _ = (Fintype.card ι + 1) •
          (Y.restrictMultiplicitySlice n).shadingMass := by
        rw [Finset.card_range, Y.shadingMass_restrictMultiplicitySlice]
  · intro x hx
    exact Y.pointMultiplicity_restrictMultiplicitySlice_eq n x hx

end

end Submission.Kakeya.ConvexGeometry
