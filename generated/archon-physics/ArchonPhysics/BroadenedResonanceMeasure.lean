import ArchonPhysics.LocalCollisionDensityTransfer
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Fixed-time broadened resonance measures

For a finite measure and a measurable real mismatch observable, a positive
observation time defines a new finite measure by weighting with the normalized
finite-time resonance kernel.  This module records the exact test-function and
mass formulas, together with a quantitative mass bound away from the resonance
set.

These are fixed-time statements.  No weak limit as the observation time tends
to infinity, and no support theorem on the exact resonance set, is asserted.
-/

namespace ArchonPhysics.BroadenedResonanceMeasure

open scoped ENNReal

open ArchonPhysics.LocalCollisionDensityTransfer
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.UniformCollisionDensityTransfer
open MeasureTheory Set

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- The nonnegative extended-real density obtained by testing a mismatch with
the normalized finite-time resonance kernel. -/
def broadenedResonanceDensity
    (mismatch : X -> Real) (T : Real) (x : X) : ENNReal :=
  ENNReal.ofReal (normalizedFiniteTimeResonanceKernel (mismatch x) T)

/-- A measurable mismatch gives a measurable broadened density at positive
observation time. -/
theorem measurable_broadenedResonanceDensity
    {mismatch : X -> Real} (hmismatch : Measurable mismatch)
    {T : Real} (hT : 0 < T) :
    Measurable (broadenedResonanceDensity mismatch T) := by
  unfold broadenedResonanceDensity
  exact ENNReal.measurable_ofReal.comp
    ((continuous_normalizedFiniteTimeResonanceKernel hT).measurable.comp hmismatch)

omit [MeasurableSpace X] in
/-- The normalized resonance density is bounded by a finite constant at every
positive observation time. -/
theorem broadenedResonanceDensity_le
    (mismatch : X -> Real) {T : Real} (hT : 0 < T) (x : X) :
    broadenedResonanceDensity mismatch T x <=
      ENNReal.ofReal ((T / 2) * sincSquareMass⁻¹) := by
  unfold broadenedResonanceDensity
  exact ENNReal.ofReal_le_ofReal
    (normalizedFiniteTimeResonanceKernel_le (mismatch x) hT)

/-- The finite measure obtained by weighting `mu` with the normalized
finite-time resonance kernel evaluated at `mismatch`. -/
def broadenedResonanceMeasure
    (mu : FiniteMeasure X) (mismatch : X -> Real)
    (_hmismatch : Measurable mismatch) (T : Real) (hT : 0 < T) :
    FiniteMeasure X := by
  let density := broadenedResonanceDensity mismatch T
  have hfinite :
      (∫⁻ x, density x ∂(mu : Measure X)) < ∞ := by
    calc
      (∫⁻ x, density x ∂(mu : Measure X)) <=
          ∫⁻ _x, ENNReal.ofReal ((T / 2) * sincSquareMass⁻¹)
            ∂(mu : Measure X) := by
        apply lintegral_mono
        intro x
        exact broadenedResonanceDensity_le mismatch hT x
      _ < ∞ := lintegral_const_lt_top ENNReal.ofReal_ne_top
  exact ⟨(mu : Measure X).withDensity density,
    isFiniteMeasure_withDensity hfinite.ne⟩

/-- Integrating a test function against the broadened measure is exactly
integration against the original measure with the resonance-kernel weight. -/
theorem integral_broadenedResonanceMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (mu : FiniteMeasure X) {mismatch : X -> Real}
    (hmismatch : Measurable mismatch) {T : Real} (hT : 0 < T)
    (test : X -> E) :
    (∫ x, test x
      ∂(broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X)) =
      ∫ x, normalizedFiniteTimeResonanceKernel (mismatch x) T • test x
        ∂(mu : Measure X) := by
  change
    (∫ x, test x
      ∂(mu : Measure X).withDensity
        (broadenedResonanceDensity mismatch T)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_broadenedResonanceDensity hmismatch hT)
    (Filter.Eventually.of_forall fun _x => ENNReal.ofReal_lt_top) test]
  apply integral_congr_ae
  filter_upwards with x
  rw [broadenedResonanceDensity, ENNReal.toReal_ofReal
    (normalizedFiniteTimeResonanceKernel_nonneg (mismatch x) T)]

/-- The real total mass of the broadened finite measure is the original
measure integral of the normalized resonance weight. -/
theorem broadenedResonanceMeasure_mass_eq_integral
    (mu : FiniteMeasure X) {mismatch : X -> Real}
    (hmismatch : Measurable mismatch) {T : Real} (hT : 0 < T) :
    ((broadenedResonanceMeasure mu mismatch hmismatch T hT).mass : Real) =
      ∫ x, normalizedFiniteTimeResonanceKernel (mismatch x) T
        ∂(mu : Measure X) := by
  simpa [FiniteMeasure.mass] using
    (integral_broadenedResonanceMeasure mu hmismatch hT
      (fun _x : X => (1 : Real)))

/-- The closed region where the mismatch stays at least `delta` away from
zero. -/
def offResonanceSet (mismatch : X -> Real) (delta : Real) : Set X :=
  {x | delta <= |mismatch x|}

theorem measurableSet_offResonanceSet
    {mismatch : X -> Real} (hmismatch : Measurable mismatch)
    (delta : Real) : MeasurableSet (offResonanceSet mismatch delta) := by
  unfold offResonanceSet
  simpa [Real.norm_eq_abs] using
    (measurableSet_le measurable_const hmismatch.norm)

/-- At fixed positive time, the broadened mass carried by mismatches at least
`delta` away from resonance is bounded by the off-gap coefficient times the
original total mass. -/
theorem broadenedResonanceMeasure_offResonanceSet_le
    (mu : FiniteMeasure X) {mismatch : X -> Real}
    (hmismatch : Measurable mismatch) {T delta : Real}
    (hT : 0 < T) (hdelta : 0 < delta) :
    ((broadenedResonanceMeasure mu mismatch hmismatch T hT)
        (offResonanceSet mismatch delta) : ENNReal) <=
      ENNReal.ofReal (offGapCoefficient delta T) * (mu.mass : ENNReal) := by
  rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change
    (mu : Measure X).withDensity (broadenedResonanceDensity mismatch T)
        (offResonanceSet mismatch delta) <= _
  rw [withDensity_apply _ (measurableSet_offResonanceSet hmismatch delta)]
  calc
    (∫⁻ x in offResonanceSet mismatch delta,
        broadenedResonanceDensity mismatch T x ∂(mu : Measure X)) <=
        ∫⁻ _x in offResonanceSet mismatch delta,
          ENNReal.ofReal (offGapCoefficient delta T) ∂(mu : Measure X) := by
      apply setLIntegral_mono measurable_const
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      exact normalizedFiniteTimeResonanceKernel_le_offGapCoefficient
        hdelta hT hx
    _ = ENNReal.ofReal (offGapCoefficient delta T) *
        (mu : Measure X) (offResonanceSet mismatch delta) := by
      rw [setLIntegral_const]
    _ <= ENNReal.ofReal (offGapCoefficient delta T) *
        (mu : Measure X) Set.univ := by
      exact mul_le_mul_right
        (measure_mono (μ := (mu : Measure X))
          (subset_univ (offResonanceSet mismatch delta))) _
    _ = ENNReal.ofReal (offGapCoefficient delta T) *
        (mu.mass : ENNReal) := by
      rw [FiniteMeasure.ennreal_mass]

end

end ArchonPhysics.BroadenedResonanceMeasure
