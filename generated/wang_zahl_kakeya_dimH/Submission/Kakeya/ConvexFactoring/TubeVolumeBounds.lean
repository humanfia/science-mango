import Submission.Kakeya.ConvexFactoring.TubeFrameBoxDimensions
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure

/-!
# Explicit volume bounds for closed tubes

This module derives algebraic measure consequences of the explicit
`HasBoxDimensions 2` certificate for a closed tube of radius at most one
half. All bounds remain valid at `δ = 0`; no argument divides by the radius.
-/

open scoped ENNReal NNReal Pointwise
open MeasureTheory

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- The exact volume sandwich supplied by the aligned frame-box certificate. -/
theorem Tube.volume_sandwich_of_le_half {δ : ℝ≥0} (T : Tube δ)
    (hδ : δ ≤ (2 : ℝ≥0)⁻¹) :
    ((2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ 2 *
          (1 + 2 * (δ : ℝ≥0∞)) ≤ volume T.carrier) ∧
      volume T.carrier ≤
        4 * (δ : ℝ≥0∞) ^ 2 * (1 + 2 * (δ : ℝ≥0∞)) := by
  have h := (T.hasBoxDimensions_frameBoxSides hδ).volume_sandwich
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  constructor
  · calc
      (2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ 2 *
          (1 + 2 * (δ : ℝ≥0∞)) =
          (2 : ℝ≥0∞)⁻¹ ^ 3 *
            (2 * (δ : ℝ≥0∞) * (2 * (δ : ℝ≥0∞)) *
              (1 + 2 * (δ : ℝ≥0∞))) := by
                calc
                  _ = (((2 : ℝ≥0∞)⁻¹ * 2) * ((2 : ℝ≥0∞)⁻¹ * 2) *
                      (2 : ℝ≥0∞)⁻¹) * (δ : ℝ≥0∞) ^ 2 *
                        (1 + 2 * (δ : ℝ≥0∞)) := by simp [htwo]
                  _ = _ := by ring
      _ ≤ volume T.carrier := by
        simpa [Tube.frameBoxSides, Tube.coe_body, Fin.prod_univ_three] using h.1
  · calc
      volume T.carrier ≤
          2 * (δ : ℝ≥0∞) * (2 * (δ : ℝ≥0∞)) *
            (1 + 2 * (δ : ℝ≥0∞)) := by
              simpa [Tube.frameBoxSides, Tube.coe_body, Fin.prod_univ_three] using h.2
      _ = 4 * (δ : ℝ≥0∞) ^ 2 * (1 + 2 * (δ : ℝ≥0∞)) := by
        ring

/-- Uniform lower bound by one half of the squared tube radius. -/
theorem Tube.half_sq_le_volume_of_le_half {δ : ℝ≥0} (T : Tube δ)
    (hδ : δ ≤ (2 : ℝ≥0)⁻¹) :
    (δ : ℝ≥0∞) ^ 2 / 2 ≤ volume T.carrier := by
  have h := (T.volume_sandwich_of_le_half hδ).1
  calc
    (δ : ℝ≥0∞) ^ 2 / 2 =
        ((2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ 2) * 1 := by
          rw [ENNReal.div_eq_inv_mul, mul_one]
    _ ≤ ((2 : ℝ≥0∞)⁻¹ * (δ : ℝ≥0∞) ^ 2) *
        (1 + 2 * (δ : ℝ≥0∞)) := by
          exact mul_le_mul_of_nonneg_left (by simp) (by exact bot_le)
    _ ≤ volume T.carrier := h

/-- Uniform upper bound by eight times the squared tube radius. -/
theorem Tube.volume_le_eight_mul_sq_of_le_half {δ : ℝ≥0} (T : Tube δ)
    (hδ : δ ≤ (2 : ℝ≥0)⁻¹) :
    volume T.carrier ≤ 8 * (δ : ℝ≥0∞) ^ 2 := by
  have h := (T.volume_sandwich_of_le_half hδ).2
  have hδe0 :
      (δ : ℝ≥0∞) ≤ (((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hδ
  have hδe : (δ : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ := by
    simpa only [ENNReal.coe_inv_two] using hδe0
  have htwo : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have htwoδ : 2 * (δ : ℝ≥0∞) ≤ 1 := by
    calc
      2 * (δ : ℝ≥0∞) ≤ 2 * (2 : ℝ≥0∞)⁻¹ :=
        mul_le_mul_of_nonneg_left hδe (by exact bot_le)
      _ = 1 := htwo
  have hfactor : 1 + 2 * (δ : ℝ≥0∞) ≤ 2 := by
    calc
      1 + 2 * (δ : ℝ≥0∞) ≤ 1 + 1 := add_le_add le_rfl htwoδ
      _ = 2 := by norm_num
  calc
    volume T.carrier ≤
        4 * (δ : ℝ≥0∞) ^ 2 * (1 + 2 * (δ : ℝ≥0∞)) := h
    _ ≤ 4 * (δ : ℝ≥0∞) ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hfactor (by exact bot_le)
    _ = 8 * (δ : ℝ≥0∞) ^ 2 := by ring

/-- A closed tube of radius at most one half has volume comparable to `δ²`
with explicit constants. -/
theorem Tube.volume_comparable_sq_of_le_half {δ : ℝ≥0} (T : Tube δ)
    (hδ : δ ≤ (2 : ℝ≥0)⁻¹) :
    ((δ : ℝ≥0∞) ^ 2 / 2 ≤ volume T.carrier) ∧
      volume T.carrier ≤ 8 * (δ : ℝ≥0∞) ^ 2 :=
  ⟨T.half_sq_le_volume_of_le_half hδ,
    T.volume_le_eight_mul_sq_of_le_half hδ⟩

end

end Submission.Kakeya.ConvexGeometry
