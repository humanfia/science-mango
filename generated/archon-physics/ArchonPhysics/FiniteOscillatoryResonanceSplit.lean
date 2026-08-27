import ArchonPhysics.NonresonantOscillatoryGain

/-!
# Finite oscillatory resonance split

A finite oscillatory interaction sum splits exactly into its resonant and
nonresonant sectors.  Exact resonances retain their secular time factor,
whereas every nonresonant term receives the inverse-mismatch bound from
`NonresonantOscillatoryGain`.

The finite index set is explicit, while the classical decisions used to form
its resonance filters are internal and impose no extra public typeclass
assumptions.  The inverse-mismatch sum is attached to the supplied finite
set; no lower mismatch gap uniform in lattice size or a thermodynamic limit
is asserted.
-/

namespace ArchonPhysics.FiniteOscillatoryResonanceSplit

open scoped BigOperators
open NonresonantOscillatoryGain

noncomputable section

variable {ι : Type*}

/-- Indices whose supplied phase mismatch vanishes exactly. -/
def resonantIndices (indices : Finset ι) (mismatch : ι → Real) : Finset ι := by
  classical
  exact indices.filter fun α ↦ mismatch α = 0

/-- Indices whose supplied phase mismatch is nonzero. -/
def nonresonantIndices (indices : Finset ι) (mismatch : ι → Real) : Finset ι := by
  classical
  exact indices.filter fun α ↦ mismatch α ≠ 0

/-- A finite sum of coefficients weighted by their oscillatory time factors. -/
def oscillatorySum (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) : Complex :=
  ∑ α ∈ indices, coefficient α * oscillatoryIntegral (mismatch α) time

/-- The exact-resonance part of a finite oscillatory sum. -/
def resonantOscillatorySum (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) : Complex :=
  ∑ α ∈ resonantIndices indices mismatch,
    coefficient α * oscillatoryIntegral (mismatch α) time

/-- The nonresonant part of a finite oscillatory sum. -/
def nonresonantOscillatorySum (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) : Complex :=
  ∑ α ∈ nonresonantIndices indices mismatch,
    coefficient α * oscillatoryIntegral (mismatch α) time

/-- The finite oscillatory sum is exactly its resonant sector plus its
nonresonant sector. -/
theorem oscillatorySum_eq_resonant_add_nonresonant
    (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) :
    oscillatorySum indices coefficient mismatch time =
      resonantOscillatorySum indices coefficient mismatch time +
        nonresonantOscillatorySum indices coefficient mismatch time := by
  classical
  simpa [oscillatorySum, resonantOscillatorySum,
    nonresonantOscillatorySum, resonantIndices, nonresonantIndices] using
    (Finset.sum_filter_add_sum_filter_not indices
      (fun α ↦ mismatch α = 0)
      (fun α ↦ coefficient α * oscillatoryIntegral (mismatch α) time)).symm

/-- Exact resonances retain precisely the elapsed-time factor. -/
theorem resonantOscillatorySum_eq_time_sum
    (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) :
    resonantOscillatorySum indices coefficient mismatch time =
      (∑ α ∈ resonantIndices indices mismatch, coefficient α) * time := by
  classical
  rw [resonantOscillatorySum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α hα
  have hMismatch : mismatch α = 0 := by
    have hα' : α ∈ indices ∧ mismatch α = 0 := by
      simpa only [resonantIndices, Finset.mem_filter] using hα
    exact hα'.2
  simp [hMismatch]

/-- The exact split with the secular resonant term displayed explicitly. -/
theorem oscillatorySum_eq_resonant_time_add_nonresonant
    (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) :
    oscillatorySum indices coefficient mismatch time =
      (∑ α ∈ resonantIndices indices mismatch, coefficient α) * time +
        nonresonantOscillatorySum indices coefficient mismatch time := by
  classical
  rw [oscillatorySum_eq_resonant_add_nonresonant,
    resonantOscillatorySum_eq_time_sum]

/-- The nonresonant sector is bounded by the finite inverse-mismatch sum,
uniformly in the elapsed time. -/
theorem norm_nonresonantOscillatorySum_le
    (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) :
    ‖nonresonantOscillatorySum indices coefficient mismatch time‖ ≤
      2 * ∑ α ∈ nonresonantIndices indices mismatch,
        ‖coefficient α‖ / |mismatch α| := by
  classical
  rw [nonresonantOscillatorySum]
  calc
    ‖∑ α ∈ nonresonantIndices indices mismatch,
        coefficient α * oscillatoryIntegral (mismatch α) time‖ ≤
        ∑ α ∈ nonresonantIndices indices mismatch,
          ‖coefficient α * oscillatoryIntegral (mismatch α) time‖ :=
      norm_sum_le _ _
    _ ≤ ∑ α ∈ nonresonantIndices indices mismatch,
          2 * (‖coefficient α‖ / |mismatch α|) := by
      apply Finset.sum_le_sum
      intro α hα
      have hMismatch : mismatch α ≠ 0 := by
        have hα' : α ∈ indices ∧ mismatch α ≠ 0 := by
          simpa only [nonresonantIndices, Finset.mem_filter] using hα
        exact hα'.2
      rw [norm_mul]
      calc
        ‖coefficient α‖ * ‖oscillatoryIntegral (mismatch α) time‖ ≤
            ‖coefficient α‖ * (2 / |mismatch α|) :=
          mul_le_mul_of_nonneg_left
            (norm_oscillatoryIntegral_le_two_div_abs hMismatch)
            (norm_nonneg _)
        _ = 2 * (‖coefficient α‖ / |mismatch α|) := by ring
    _ = 2 * ∑ α ∈ nonresonantIndices indices mismatch,
          ‖coefficient α‖ / |mismatch α| := by
      rw [Finset.mul_sum]

/-- A real perturbative coupling multiplying the nonresonant sector. -/
def coupledNonresonantOscillatorySum (coupling : Real)
    (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) : Complex :=
  coupling * nonresonantOscillatorySum indices coefficient mismatch time

/-- After multiplication by a coupling, the nonresonant sector is `O(|g|)`
with an explicit constant independent of time.  No size-uniform control of the
displayed inverse-mismatch sum is claimed. -/
theorem norm_coupledNonresonantOscillatorySum_le
    (coupling : Real) (indices : Finset ι) (coefficient : ι → Complex)
    (mismatch : ι → Real) (time : Real) :
    ‖coupledNonresonantOscillatorySum coupling indices coefficient mismatch time‖ ≤
      2 * |coupling| * ∑ α ∈ nonresonantIndices indices mismatch,
        ‖coefficient α‖ / |mismatch α| := by
  classical
  rw [coupledNonresonantOscillatorySum, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    |coupling| * ‖nonresonantOscillatorySum indices coefficient mismatch time‖ ≤
        |coupling| * (2 * ∑ α ∈ nonresonantIndices indices mismatch,
          ‖coefficient α‖ / |mismatch α|) :=
      mul_le_mul_of_nonneg_left
        (norm_nonresonantOscillatorySum_le indices coefficient mismatch time)
        (abs_nonneg coupling)
    _ = 2 * |coupling| * ∑ α ∈ nonresonantIndices indices mismatch,
          ‖coefficient α‖ / |mismatch α| := by ring

end

end ArchonPhysics.FiniteOscillatoryResonanceSplit
