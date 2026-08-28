import ArchonPhysics.NestedOscillatoryIntegral

/-!
# Finite extraction of an effective interaction from a nested Picard term

For a nonresonant inner quadratic interaction, the exact second-Picard
coefficient is a divided difference.  Summing this identity over a finite
diagram family separates an effective higher-order oscillatory interaction
from a normal-form boundary correction.

This is the finite algebraic step by which an alpha-FPUT quadratic modal
source generates an effective four-wave source after the forbidden
three-wave channel is removed.  No kinetic limit or resonance-counting
claim is made here.
-/

namespace ArchonPhysics.FiniteNestedNormalFormExtraction

open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain

noncomputable section

variable {Diagram : Type*} [Fintype Diagram]

/-- The exact finite second-Picard sum before normal-form extraction. -/
def finiteNestedPicardSum
    (coefficient : Diagram -> Complex)
    (outerMismatch innerMismatch : Diagram -> Real)
    (time : Real) : Complex :=
  ∑ diagram,
    coefficient diagram *
      nestedOscillatoryIntegral
        (outerMismatch diagram) (innerMismatch diagram) time

/-- The effective higher-order part, carrying the sum of the outer and inner
mismatches. -/
def finiteEffectiveInteractionSum
    (coefficient : Diagram -> Complex)
    (outerMismatch innerMismatch : Diagram -> Real)
    (time : Real) : Complex :=
  ∑ diagram,
    coefficient diagram / (Complex.I * innerMismatch diagram) *
      oscillatoryIntegral
        (outerMismatch diagram + innerMismatch diagram) time

/-- The finite endpoint correction created by the first normal-form
transformation. -/
def finiteNormalFormBoundarySum
    (coefficient : Diagram -> Complex)
    (outerMismatch innerMismatch : Diagram -> Real)
    (time : Real) : Complex :=
  ∑ diagram,
    coefficient diagram / (Complex.I * innerMismatch diagram) *
      oscillatoryIntegral (outerMismatch diagram) time

/-- Exact finite normal-form extraction.  The only hypothesis is that every
inner mismatch appearing in the finite family is nonzero. -/
theorem finiteNestedPicardSum_eq_effective_sub_boundary
    (coefficient : Diagram -> Complex)
    (outerMismatch innerMismatch : Diagram -> Real)
    (time : Real)
    (hinner : ∀ diagram, innerMismatch diagram ≠ 0) :
    finiteNestedPicardSum coefficient outerMismatch innerMismatch time =
      finiteEffectiveInteractionSum coefficient outerMismatch innerMismatch time -
        finiteNormalFormBoundarySum coefficient outerMismatch innerMismatch time := by
  unfold finiteNestedPicardSum finiteEffectiveInteractionSum
    finiteNormalFormBoundarySum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro diagram _hdiagram
  rw [nestedOscillatoryIntegral_eq_sub_div (hinner diagram)]
  ring

/-- The effective sum splits exactly into its total-resonant and
total-nonresonant sectors. -/
theorem finiteEffectiveInteractionSum_eq_resonant_add_nonresonant
    (coefficient : Diagram -> Complex)
    (outerMismatch innerMismatch : Diagram -> Real)
    (time : Real) :
    finiteEffectiveInteractionSum coefficient outerMismatch innerMismatch time =
      (∑ diagram,
        if outerMismatch diagram + innerMismatch diagram = 0 then
          coefficient diagram / (Complex.I * innerMismatch diagram) * time
        else 0) +
      (∑ diagram,
        if outerMismatch diagram + innerMismatch diagram ≠ 0 then
          coefficient diagram / (Complex.I * innerMismatch diagram) *
            oscillatoryIntegral
              (outerMismatch diagram + innerMismatch diagram) time
        else 0) := by
  unfold finiteEffectiveInteractionSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro diagram _hdiagram
  by_cases htotal : outerMismatch diagram + innerMismatch diagram = 0
  · rw [if_pos htotal, if_neg (not_not.mpr htotal), htotal,
      oscillatoryIntegral_zero]
    ring
  · rw [if_neg htotal, if_pos htotal]
    ring

omit [Fintype Diagram] in
/-- A positive inner-mismatch gap bounds every inverse divisor in the
effective coefficient. -/
theorem norm_inverse_inner_divisor_le
    (innerMismatch : Diagram -> Real) (gap : Real) (hgap : 0 < gap)
    (hinner : ∀ diagram, gap ≤ |innerMismatch diagram|)
    (diagram : Diagram) :
    ‖((1 : Complex) / (Complex.I * innerMismatch diagram))‖ ≤ 1 / gap := by
  have hnonzero : innerMismatch diagram ≠ 0 := by
    intro hzero
    have hbound := hinner diagram
    rw [hzero, abs_zero] at hbound
    exact (not_lt_of_ge hbound) hgap
  rw [norm_div, norm_one, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact div_le_div_of_nonneg_left zero_le_one hgap (hinner diagram)

/-- The endpoint correction has a direct finite bound from the inner gap and
the elapsed time. -/
theorem norm_finiteNormalFormBoundarySum_le
    (coefficient : Diagram -> Complex)
    (outerMismatch innerMismatch : Diagram -> Real)
    (time gap : Real) (hgap : 0 < gap)
    (hinner : ∀ diagram, gap ≤ |innerMismatch diagram|) :
    ‖finiteNormalFormBoundarySum
        coefficient outerMismatch innerMismatch time‖ ≤
      (|time| / gap) * ∑ diagram, ‖coefficient diagram‖ := by
  unfold finiteNormalFormBoundarySum
  calc
    ‖∑ diagram,
        coefficient diagram / (Complex.I * innerMismatch diagram) *
          oscillatoryIntegral (outerMismatch diagram) time‖ ≤
      ∑ diagram,
        ‖coefficient diagram / (Complex.I * innerMismatch diagram) *
          oscillatoryIntegral (outerMismatch diagram) time‖ := norm_sum_le _ _
    _ ≤ ∑ diagram, (|time| / gap) * ‖coefficient diagram‖ := by
      apply Finset.sum_le_sum
      intro diagram _hdiagram
      have hinverse := norm_inverse_inner_divisor_le
        innerMismatch gap hgap hinner diagram
      have hosc := norm_oscillatoryIntegral_le_abs_time
        (outerMismatch diagram) time
      rw [norm_mul, norm_div]
      calc
        ‖coefficient diagram‖ /
              ‖Complex.I * (innerMismatch diagram : Complex)‖ *
              ‖oscillatoryIntegral (outerMismatch diagram) time‖ ≤
            ‖coefficient diagram‖ * (1 / gap) * |time| := by
          have hfactor :
              1 / ‖Complex.I * (innerMismatch diagram : Complex)‖ ≤
                1 / gap := by
            simpa [norm_div, norm_one] using hinverse
          have hfactor' :
              ‖Complex.I * (innerMismatch diagram : Complex)‖⁻¹ ≤
                1 / gap := by
            simpa [one_div] using hfactor
          rw [div_eq_mul_inv]
          gcongr
        _ = (|time| / gap) * ‖coefficient diagram‖ := by ring
    _ = (|time| / gap) * ∑ diagram, ‖coefficient diagram‖ := by
      rw [Finset.mul_sum]

end

end ArchonPhysics.FiniteNestedNormalFormExtraction
