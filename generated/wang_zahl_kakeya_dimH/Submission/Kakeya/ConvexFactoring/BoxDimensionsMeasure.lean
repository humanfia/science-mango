import Submission.Kakeya.ConvexFactoring.FrameBoxVolume

/-!
# Measure consequences of certified box dimensions

This file derives volume estimates only from an existing
`HasBoxDimensions` certificate. It does not assert existence of a John
ellipsoid or of any particular witness box.
-/

open scoped ENNReal NNReal Pointwise
open MeasureTheory

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

variable {C θ a b : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}

/-- The inner and outer witness boxes give an explicit volume sandwich. -/
theorem HasBoxDimensions.volume_sandwich
    (h : HasBoxDimensions C side K) :
    ((↑(C⁻¹) : ℝ≥0∞) ^ 3 * ∏ i, (side i : ℝ≥0∞) ≤
        volume (K : Set Space)) ∧
      volume (K : Set Space) ≤ ∏ i, (side i : ℝ≥0∞) := by
  rcases h with ⟨_, box, hside, hinner, houter⟩
  constructor
  · calc
      (↑(C⁻¹) : ℝ≥0∞) ^ 3 * ∏ i, (side i : ℝ≥0∞) =
          volume ((box.rescale C⁻¹).body : Set Space) := by
        rw [FrameBox.coe_body, FrameBox.volume_rescale,
          FrameBox.volume_carrier, hside]
      _ ≤ volume (K : Set Space) := measure_mono hinner
  · calc
      volume (K : Set Space) ≤ volume (box.body : Set Space) :=
        measure_mono houter
      _ = ∏ i, (side i : ℝ≥0∞) := by
        rw [FrameBox.volume_body, hside]

/-- Lower half of the certified volume sandwich. -/
theorem HasBoxDimensions.volume_lower_bound
    (h : HasBoxDimensions C side K) :
    (↑(C⁻¹) : ℝ≥0∞) ^ 3 * ∏ i, (side i : ℝ≥0∞) ≤
      volume (K : Set Space) :=
  h.volume_sandwich.1

/-- Upper half of the certified volume sandwich. -/
theorem HasBoxDimensions.volume_upper_bound
    (h : HasBoxDimensions C side K) :
    volume (K : Set Space) ≤ ∏ i, (side i : ℝ≥0∞) :=
  h.volume_sandwich.2

/-- A body with certified box dimensions has finite ambient volume. -/
theorem HasBoxDimensions.volume_lt_top
    (h : HasBoxDimensions C side K) :
    volume (K : Set Space) < ∞ := by
  refine h.volume_upper_bound.trans_lt (ENNReal.prod_lt_top ?_)
  intro i hi
  exact ENNReal.coe_lt_top

/-- Positive side lengths and the built-in condition `1 ≤ C` force positive
volume, via the inner witness box. -/
theorem HasBoxDimensions.volume_pos
    (h : HasBoxDimensions C side K)
    (hsidePos : ∀ i, 0 < side i) :
    0 < volume (K : Set Space) := by
  rcases h with ⟨hC, box, hside, hinner, _⟩
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hinnerPos : 0 < volume ((box.rescale C⁻¹).body : Set Space) := by
    apply FrameBox.volume_body_pos
    intro i
    rw [FrameBox.rescale_side]
    apply mul_pos
    · exact inv_pos.mpr hCpos
    · simpa [hside] using hsidePos i
  exact hinnerPos.trans_le (measure_mono hinner)

/-- A certified slab has volume between the expected explicit multiples of
its thickness. -/
theorem IsSlab.volume_sandwich
    (h : IsSlab C θ K) :
    ((↑(C⁻¹) : ℝ≥0∞) ^ 3 * (θ : ℝ≥0∞) ≤ volume (K : Set Space)) ∧
      volume (K : Set Space) ≤ (θ : ℝ≥0∞) := by
  rcases h with ⟨_, _, hbox⟩
  simpa [slabSides, Fin.prod_univ_succ] using hbox.volume_sandwich

/-- Explicit lower volume bound for a certified slab. -/
theorem IsSlab.volume_lower_bound
    (h : IsSlab C θ K) :
    (↑(C⁻¹) : ℝ≥0∞) ^ 3 * (θ : ℝ≥0∞) ≤ volume (K : Set Space) :=
  h.volume_sandwich.1

/-- Explicit upper volume bound for a certified slab. -/
theorem IsSlab.volume_upper_bound
    (h : IsSlab C θ K) :
    volume (K : Set Space) ≤ (θ : ℝ≥0∞) :=
  h.volume_sandwich.2

/-- A certified slab has positive volume. -/
theorem IsSlab.volume_pos
    (h : IsSlab C θ K) :
    0 < volume (K : Set Space) := by
  rcases h with ⟨hθ, _, hbox⟩
  apply hbox.volume_pos
  intro i
  fin_cases i <;> simp [slabSides, hθ]

/-- A certified plank has volume between the expected explicit multiples of
the product of its two short dimensions. -/
theorem IsPlank.volume_sandwich
    (h : IsPlank C a b K) :
    ((↑(C⁻¹) : ℝ≥0∞) ^ 3 * ((a : ℝ≥0∞) * (b : ℝ≥0∞)) ≤
        volume (K : Set Space)) ∧
      volume (K : Set Space) ≤ (a : ℝ≥0∞) * (b : ℝ≥0∞) := by
  rcases h with ⟨_, _, _, hbox⟩
  simpa [plankSides, Fin.prod_univ_succ] using hbox.volume_sandwich

/-- Explicit lower volume bound for a certified plank. -/
theorem IsPlank.volume_lower_bound
    (h : IsPlank C a b K) :
    (↑(C⁻¹) : ℝ≥0∞) ^ 3 * ((a : ℝ≥0∞) * (b : ℝ≥0∞)) ≤
      volume (K : Set Space) :=
  h.volume_sandwich.1

/-- Explicit upper volume bound for a certified plank. -/
theorem IsPlank.volume_upper_bound
    (h : IsPlank C a b K) :
    volume (K : Set Space) ≤ (a : ℝ≥0∞) * (b : ℝ≥0∞) :=
  h.volume_sandwich.2

/-- A certified plank has positive volume. -/
theorem IsPlank.volume_pos
    (h : IsPlank C a b K) :
    0 < volume (K : Set Space) := by
  rcases h with ⟨ha, hab, _, hbox⟩
  have hb : 0 < b := ha.trans_le hab
  apply hbox.volume_pos
  intro i
  fin_cases i <;> simp [plankSides, ha, hb]

end

end Submission.Kakeya.ConvexGeometry
