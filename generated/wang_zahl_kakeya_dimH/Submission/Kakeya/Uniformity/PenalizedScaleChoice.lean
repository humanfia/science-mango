import Submission.Kakeya.Uniformity.Pigeonhole

set_option autoImplicit false

open scoped ENNReal

namespace Submission.Kakeya.Uniformity

noncomputable section

/-- A scale chosen by maximizing density divided by a positive finite penalty. -/
structure PenalizedScaleChoice {σ : Type*}
    (scales : Finset σ) (density penalty : σ → ℝ≥0∞) where
  index : σ
  index_mem : index ∈ scales
  maximal : ∀ s ∈ scales,
    density s / penalty s ≤ density index / penalty index

/-- The finite penalized scale maximizer exists without a compactness input. -/
theorem exists_penalizedScaleChoice {σ : Type*}
    (scales : Finset σ) (density penalty : σ → ℝ≥0∞)
    (hscales : scales.Nonempty) :
    Nonempty (PenalizedScaleChoice scales density penalty) := by
  classical
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image scales
    (fun s => density s / penalty s) hscales
  exact ⟨⟨r, hr, fun s hs => hmax s hs⟩⟩

/-- Penalized maximality gives the zero-division-safe cross-stability
inequality. -/
theorem PenalizedScaleChoice.cross_stable {σ : Type*}
    {scales : Finset σ} {density penalty : σ → ℝ≥0∞}
    (C : PenalizedScaleChoice scales density penalty)
    (hpenalty0 : ∀ s ∈ scales, penalty s ≠ 0)
    (hpenaltyTop : ∀ s ∈ scales, penalty s ≠ ∞)
    {s : σ} (hs : s ∈ scales) :
    density s * penalty C.index ≤
      density C.index * penalty s := by
  have hscore := C.maximal s hs
  have hs0 := hpenalty0 s hs
  have hsTop := hpenaltyTop s hs
  have hr0 := hpenalty0 C.index C.index_mem
  have hrTop := hpenaltyTop C.index C.index_mem
  have hdiv : density s ≤
      (density C.index / penalty C.index) * penalty s :=
    (ENNReal.div_le_iff hs0 hsTop).1 hscore
  calc
    density s * penalty C.index ≤
        ((density C.index / penalty C.index) * penalty s) *
          penalty C.index := mul_le_mul' hdiv le_rfl
    _ = ((density C.index / penalty C.index) * penalty C.index) *
          penalty s := by ac_rfl
    _ = density C.index * penalty s := by
      rw [ENNReal.div_mul_cancel hr0 hrTop]

/-- Transfer a density lower bound from an anchor scale to the selected scale.
The application-specific input is the controlled penalty ratio. -/
theorem PenalizedScaleChoice.anchor_density_le {σ : Type*}
    {scales : Finset σ} {density penalty : σ → ℝ≥0∞}
    (C : PenalizedScaleChoice scales density penalty)
    (hpenalty0 : ∀ s ∈ scales, penalty s ≠ 0)
    (hpenaltyTop : ∀ s ∈ scales, penalty s ≠ ∞)
    (anchor : σ) (hanchor : anchor ∈ scales)
    (d0 P : ℝ≥0∞) (hanchorDensity : d0 ≤ density anchor)
    (hpenaltyRatio : penalty anchor ≤ P * penalty C.index) :
    d0 ≤ P * density C.index := by
  have hstable := C.cross_stable hpenalty0 hpenaltyTop hanchor
  have hbeforeCancel : d0 * penalty C.index ≤
      (P * density C.index) * penalty C.index := by
    calc
      d0 * penalty C.index ≤ density anchor * penalty C.index :=
        mul_le_mul' hanchorDensity le_rfl
      _ ≤ density C.index * penalty anchor := hstable
      _ ≤ density C.index * (P * penalty C.index) :=
        mul_le_mul' le_rfl hpenaltyRatio
      _ = (P * density C.index) * penalty C.index := by ac_rfl
  exact (ENNReal.mul_le_mul_iff_left
    (hpenalty0 C.index C.index_mem)
    (hpenaltyTop C.index C.index_mem)).1 hbeforeCancel

/-- Bundle the actual finite maximizer, cross stability at every admissible
scale, and the anchored quantitative density lower bound. -/
theorem exists_penalizedScaleChoice_anchored {σ : Type*}
    (scales : Finset σ) (density penalty : σ → ℝ≥0∞)
    (hscales : scales.Nonempty)
    (hpenalty0 : ∀ s ∈ scales, penalty s ≠ 0)
    (hpenaltyTop : ∀ s ∈ scales, penalty s ≠ ∞)
    (anchor : σ) (hanchor : anchor ∈ scales)
    (d0 P : ℝ≥0∞) (hanchorDensity : d0 ≤ density anchor)
    (hpenaltyRatio : ∀ r ∈ scales, penalty anchor ≤ P * penalty r) :
    ∃ C : PenalizedScaleChoice scales density penalty,
      (∀ s ∈ scales, density s * penalty C.index ≤
        density C.index * penalty s) ∧
      d0 ≤ P * density C.index := by
  obtain ⟨C⟩ := exists_penalizedScaleChoice scales density penalty hscales
  exact ⟨C, fun s hs => C.cross_stable hpenalty0 hpenaltyTop hs,
    C.anchor_density_le hpenalty0 hpenaltyTop anchor hanchor d0 P
      hanchorDensity (hpenaltyRatio C.index C.index_mem)⟩

end

end Submission.Kakeya.Uniformity
