import ArchonPhysics.FiniteSymmetricWindowLocalIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Quantitative integral bounds on symmetric time windows

For a probability sample measure, the product of the symmetric real-time
window `[-T,T]` with the sample space has real mass exactly `2T` when
`T >= 0`.  Uniform pointwise bounds therefore give explicit linear-in-window
Bochner and L1 estimates.  These estimates expose their window dependence;
they do not provide a kinetic-time-uniform bound.
-/

namespace ArchonPhysics.FiniteSymmetricWindowIntegralBounds

open Set
open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]
variable {probability : Measure Omega} [IsProbabilityMeasure probability]

/-- The real mass of a nonnegative symmetric time window times a probability
sample space is exactly its length `2 * window`. -/
theorem real_prod_probability_symmetricWindow
    (window : Real) (hwindow : 0 <= window) :
    ((volume.restrict (Icc (-window) window)).prod probability).real univ =
      2 * window := by
  rw [measureReal_def, Measure.prod_apply .univ]
  simp [Real.volume_Icc, hwindow]
  ring

variable {E : Type*} [NormedAddCommGroup E]

/-- A uniform norm bound gives an explicit linear-in-window bound for the
norm of the product-space Bochner integral. -/
theorem norm_integral_timeSample_le_two_mul
    [NormedSpace Real E]
    (window : Real) (hwindow : 0 <= window)
    (f : Real × Omega -> E) (C : Real)
    (hbound : ∀ᵐ st ∂((volume.restrict (Icc (-window) window)).prod
      probability), ‖f st‖ <= C) :
    ‖∫ st, f st ∂((volume.restrict (Icc (-window) window)).prod
      probability)‖ <= C * (2 * window) := by
  let _ : IsFiniteMeasure (volume.restrict (Icc (-window) window)) := by
    infer_instance
  let _ : IsFiniteMeasure
      ((volume.restrict (Icc (-window) window)).prod probability) := by
    infer_instance
  calc
    ‖∫ st, f st ∂((volume.restrict (Icc (-window) window)).prod
        probability)‖ <=
        C * ((volume.restrict (Icc (-window) window)).prod
          probability).real univ :=
      norm_integral_le_of_norm_le_const hbound
    _ = C * (2 * window) := by
      rw [real_prod_probability_symmetricWindow window hwindow]

/-- The same uniform bound controls the full L1 norm on the product window. -/
theorem integral_norm_timeSample_le_two_mul
    (window : Real) (hwindow : 0 <= window)
    (f : Real × Omega -> E) (C : Real)
    (hf : Integrable f
      ((volume.restrict (Icc (-window) window)).prod probability))
    (hbound : ∀ᵐ st ∂((volume.restrict (Icc (-window) window)).prod
      probability), ‖f st‖ <= C) :
    (∫ st, ‖f st‖ ∂((volume.restrict (Icc (-window) window)).prod
      probability)) <= C * (2 * window) := by
  let _ : IsFiniteMeasure (volume.restrict (Icc (-window) window)) := by
    infer_instance
  let _ : IsFiniteMeasure
      ((volume.restrict (Icc (-window) window)).prod probability) := by
    infer_instance
  calc
    (∫ st, ‖f st‖ ∂((volume.restrict (Icc (-window) window)).prod
        probability)) <=
        ∫ _st, C ∂((volume.restrict (Icc (-window) window)).prod
          probability) :=
      integral_mono_ae hf.norm (integrable_const C) hbound
    _ = C * ((volume.restrict (Icc (-window) window)).prod
          probability).real univ := by
      rw [integral_const, smul_eq_mul, mul_comm]
    _ = C * (2 * window) := by
      rw [real_prod_probability_symmetricWindow window hwindow]

end ArchonPhysics.FiniteSymmetricWindowIntegralBounds
