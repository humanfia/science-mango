import ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability

/-!
# Uniform frequency marginals from joint frequency--mismatch density

The normalized finite-time resonance kernel has unit mass in the mismatch
coordinate but height proportional to the observation time.  Consequently a
one-dimensional density estimate along a common-mass ray is not by itself
uniform in time: exact resonance is invariant under that scaling.

The correct input is a two-dimensional density estimate for
`(one frequency, mismatch)`.  This file proves that such an estimate survives
resonance broadening and projection to the frequency line with exactly the
same constant, independently of the broadening time.
-/

namespace ArchonPhysics.FrequencyMismatchKernelMarginalDomination

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.UniformCollisionDensityTransfer
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Retain one collision-leg frequency together with the scalar mismatch. -/
def frequencyMismatchCoordinates
    (frequency mismatch : X → Real) (x : X) : Real × Real :=
  (frequency x, mismatch x)

theorem measurable_frequencyMismatchCoordinates
    {frequency mismatch : X → Real}
    (hfrequency : Measurable frequency) (hmismatch : Measurable mismatch) :
    Measurable (frequencyMismatchCoordinates frequency mismatch) := by
  unfold frequencyMismatchCoordinates
  fun_prop

/-- A joint Lebesgue-density bound for `(frequency, mismatch)` gives a
time-uniform Lebesgue-density bound for the frequency marginal after applying
the normalized resonance kernel. -/
theorem map_frequency_broadenedResonanceMeasure_le_volume_of_joint_le
    (mu : FiniteMeasure X) {mismatch : X → Real}
    (hmismatch : Measurable mismatch) {T : Real} (hT : 0 < T)
    (frequency : X → Real) (hfrequency : Measurable frequency)
    (C : ENNReal)
    (hjoint :
      Measure.map (frequencyMismatchCoordinates frequency mismatch)
          (mu : Measure X) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map frequency
        (broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X) ≤
      C • (volume : Measure Real) := by
  let coordinates := frequencyMismatchCoordinates frequency mismatch
  let kernelDensity : Real × Real → ENNReal := fun value =>
    ENNReal.ofReal
      (normalizedFiniteTimeResonanceKernel value.2 T)
  have hcoordinates : Measurable coordinates :=
    measurable_frequencyMismatchCoordinates hfrequency hmismatch
  have hkernelDensity : Measurable kernelDensity := by
    exact ENNReal.measurable_ofReal.comp
      ((continuous_normalizedFiniteTimeResonanceKernel hT).measurable.comp
        measurable_snd)
  have hbroadLift :
      Measure.map coordinates
          (broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X) =
        (Measure.map coordinates (mu : Measure X)).withDensity kernelDensity := by
    change Measure.map coordinates
        ((mu : Measure X).withDensity
          (broadenedResonanceDensity mismatch T)) = _
    have hmap := map_withDensity_comp
      (mu : Measure X) coordinates hcoordinates kernelDensity hkernelDensity
    apply hmap.trans
    congr 2
  calc
    Measure.map frequency
        (broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X) =
        Measure.map Prod.fst
          (Measure.map coordinates
            (broadenedResonanceMeasure mu mismatch hmismatch T hT :
              Measure X)) := by
      rw [Measure.map_map measurable_fst hcoordinates]
      rfl
    _ = Measure.map Prod.fst
        ((Measure.map coordinates (mu : Measure X)).withDensity
          kernelDensity) := by rw [hbroadLift]
    _ ≤ Measure.map Prod.fst
        ((C • ((volume : Measure Real).prod
          (volume : Measure Real))).withDensity kernelDensity) :=
      Measure.map_mono
        (withDensity_mono_measure hjoint kernelDensity) measurable_fst
    _ = C • (volume : Measure Real) := by
      rw [withDensity_smul_measure, Measure.map_smul]
      change C • Measure.map Prod.fst
          (((volume : Measure Real).prod
            (volume : Measure Real)).withDensity (fun value =>
              ENNReal.ofReal
                (normalizedFiniteTimeResonanceKernel value.2 T))) = _
      have hkernelMeasurable : Measurable (fun mismatch : Real =>
          ENNReal.ofReal (normalizedFiniteTimeResonanceKernel mismatch T)) :=
        ENNReal.measurable_ofReal.comp
          (continuous_normalizedFiniteTimeResonanceKernel hT).measurable
      have hprod :
          (((volume : Measure Real).prod
            (volume : Measure Real)).withDensity (fun value =>
              ENNReal.ofReal
                (normalizedFiniteTimeResonanceKernel value.2 T))) =
            (volume : Measure Real).prod
              ((volume : Measure Real).withDensity (fun mismatch =>
                ENNReal.ofReal
                  (normalizedFiniteTimeResonanceKernel mismatch T))) := by
        simpa only [Function.comp_apply] using
          (prod_withDensity_right hkernelMeasurable).symm
      rw [hprod]
      change C • Measure.map Prod.fst
          ((volume : Measure Real).prod
            (normalizedFiniteTimeResonanceKernelFiniteMeasure T hT :
              Measure Real)) = _
      rw [Measure.map_fst_prod,
        normalizedFiniteTimeResonanceKernelFiniteMeasure_univ,
        one_smul]

/-- The same joint bound gives absolute continuity of every positive-time
broadened one-leg frequency marginal. -/
theorem map_frequency_broadenedResonanceMeasure_absolutelyContinuous_of_joint_le
    (mu : FiniteMeasure X) {mismatch : X → Real}
    (hmismatch : Measurable mismatch) {T : Real} (hT : 0 < T)
    (frequency : X → Real) (hfrequency : Measurable frequency)
    (C : ENNReal)
    (hjoint :
      Measure.map (frequencyMismatchCoordinates frequency mismatch)
          (mu : Measure X) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map frequency
        (broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X) ≪
      (volume : Measure Real) := by
  exact
    (map_frequency_broadenedResonanceMeasure_le_volume_of_joint_le
      mu hmismatch hT frequency hfrequency C hjoint).absolutelyContinuous.trans
        Measure.smul_absolutelyContinuous

end

end ArchonPhysics.FrequencyMismatchKernelMarginalDomination
