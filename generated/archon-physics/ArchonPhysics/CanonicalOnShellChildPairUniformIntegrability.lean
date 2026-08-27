import ArchonPhysics.CanonicalOnShellChildPairUpperAbsoluteContinuity
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Uniform-integrability reduction for canonical child-pair traces

The normalized sinc-squared resonance kernel has unit mass in the mismatch
coordinate.  Consequently a time-independent three-dimensional density bound
for the joint `(child pair, mismatch)` law gives a time-independent planar
density bound after broadening and forgetting mismatch.  This avoids the
linearly growing pointwise kernel-height estimate.

The module also identifies the exact lifted law whose density must be
controlled.  Thus the remaining model theorem is a quantitative
three-frequency spectral-averaging estimate, rather than an abstract
uniform-integrability assumption on the already broadened measures.
-/

namespace ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellChildPairUpperAbsoluteContinuity
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter
open scoped ENNReal

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Pushing forward a density which factors through the pushed observable is
the same as first pushing forward and then applying that density. -/
theorem map_withDensity_comp
    (mu : Measure X) (f : X -> Y) (hf : Measurable f)
    (density : Y -> ENNReal) (hdensity : Measurable density) :
    Measure.map f (mu.withDensity (density ∘ f)) =
      (Measure.map f mu).withDensity density := by
  ext s hs
  rw [Measure.map_apply hf hs,
    withDensity_apply _ (hs.preimage hf), withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage hf),
    ← lintegral_indicator hs,
    lintegral_map (hdensity.indicator hs) hf]
  congr 1

/-- With-density is monotone in its underlying measure. -/
theorem withDensity_mono_measure
    {mu nu : Measure X} (hmu : mu <= nu) (density : X -> ENNReal) :
    mu.withDensity density <= nu.withDensity density := by
  rw [Measure.le_iff]
  intro s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  exact lintegral_mono'
    (Measure.restrict_mono_measure hmu s) le_rfl

/-- The normalized finite-time sinc-squared kernel bundled as a finite
measure on the mismatch line. -/
def normalizedFiniteTimeResonanceKernelFiniteMeasure
    (T : Real) (hT : 0 < T) : FiniteMeasure Real := by
  let density : Real -> ENNReal := fun mismatch =>
    ENNReal.ofReal (normalizedFiniteTimeResonanceKernel mismatch T)
  have hfinite :
      (∫⁻ mismatch : Real, density mismatch ∂volume) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_normalizedFiniteTimeResonanceKernel hT)
      (Eventually.of_forall fun mismatch =>
        normalizedFiniteTimeResonanceKernel_nonneg mismatch T),
      integral_normalizedFiniteTimeResonanceKernel_eq_one hT]
    norm_num
  exact ⟨(volume : Measure Real).withDensity density,
    isFiniteMeasure_withDensity hfinite⟩

@[simp]
theorem normalizedFiniteTimeResonanceKernelFiniteMeasure_toMeasure
    (T : Real) (hT : 0 < T) :
    (normalizedFiniteTimeResonanceKernelFiniteMeasure T hT : Measure Real) =
      (volume : Measure Real).withDensity (fun mismatch =>
        ENNReal.ofReal
          (normalizedFiniteTimeResonanceKernel mismatch T)) := by
  rfl

/-- Exact unit mass of the bundled normalized resonance-kernel measure. -/
@[simp]
theorem normalizedFiniteTimeResonanceKernelFiniteMeasure_univ
    (T : Real) (hT : 0 < T) :
    (normalizedFiniteTimeResonanceKernelFiniteMeasure T hT : Measure Real)
        Set.univ = 1 := by
  change (volume : Measure Real).withDensity (fun mismatch =>
      ENNReal.ofReal (normalizedFiniteTimeResonanceKernel mismatch T))
    Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_normalizedFiniteTimeResonanceKernel hT)
      (Eventually.of_forall fun mismatch =>
        normalizedFiniteTimeResonanceKernel_nonneg mismatch T),
    integral_normalizedFiniteTimeResonanceKernel_eq_one hT]
  norm_num

/-- Joint coordinates retaining a planar observable together with the scalar
mismatch used by the resonance kernel. -/
def childMismatchCoordinates
    (child : X -> Real × Real) (mismatch : X -> Real)
    (x : X) : (Real × Real) × Real :=
  (child x, mismatch x)

theorem measurable_childMismatchCoordinates
    {child : X -> Real × Real} (hchild : Measurable child)
    {mismatch : X -> Real} (hmismatch : Measurable mismatch) :
    Measurable (childMismatchCoordinates child mismatch) := by
  unfold childMismatchCoordinates
  fun_prop

/-- Sharp fixed-time estimate: a uniform density bound for the lifted raw
`(child pair, mismatch)` law is preserved after applying the unit-mass
resonance kernel and projecting to the child plane.  The constant is
independent of `T`. -/
theorem map_broadenedResonanceMeasure_le_volume_of_lifted_le
    (mu : FiniteMeasure X) {mismatch : X -> Real}
    (hmismatch : Measurable mismatch) {T : Real} (hT : 0 < T)
    (child : X -> Real × Real) (hchild : Measurable child)
    (C : ENNReal)
    (hlifted :
      Measure.map (childMismatchCoordinates child mismatch) (mu : Measure X) <=
        C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))) :
    Measure.map child
        (broadenedResonanceMeasure mu mismatch hmismatch T hT : Measure X) <=
      C • (volume : Measure (Real × Real)) := by
  let coordinates := childMismatchCoordinates child mismatch
  let kernelDensity : ((Real × Real) × Real) -> ENNReal := fun value =>
    ENNReal.ofReal
      (normalizedFiniteTimeResonanceKernel value.2 T)
  have hcoordinates : Measurable coordinates :=
    measurable_childMismatchCoordinates hchild hmismatch
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
    Measure.map child
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
    _ <= Measure.map Prod.fst
        ((C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))).withDensity kernelDensity) :=
      Measure.map_mono
        (withDensity_mono_measure hlifted kernelDensity) measurable_fst
    _ = C • (volume : Measure (Real × Real)) := by
      rw [withDensity_smul_measure, Measure.map_smul]
      change C • Measure.map Prod.fst
          (((volume : Measure (Real × Real)).prod
            (volume : Measure Real)).withDensity (fun value =>
              ENNReal.ofReal
                (normalizedFiniteTimeResonanceKernel value.2 T))) = _
      have hkernelMeasurable : Measurable (fun mismatch : Real =>
          ENNReal.ofReal (normalizedFiniteTimeResonanceKernel mismatch T)) :=
        ENNReal.measurable_ofReal.comp
          (continuous_normalizedFiniteTimeResonanceKernel hT).measurable
      have hprod :
          (((volume : Measure (Real × Real)).prod
            (volume : Measure Real)).withDensity (fun value =>
              ENNReal.ofReal
                (normalizedFiniteTimeResonanceKernel value.2 T))) =
            (volume : Measure (Real × Real)).prod
              ((volume : Measure Real).withDensity (fun mismatch =>
                ENNReal.ofReal
                  (normalizedFiniteTimeResonanceKernel mismatch T))) := by
        simpa only [Function.comp_apply] using
          (prod_withDensity_right hkernelMeasurable).symm
      rw [hprod]
      change C • Measure.map Prod.fst
          ((volume : Measure (Real × Real)).prod
            (normalizedFiniteTimeResonanceKernelFiniteMeasure T hT :
              Measure Real)) = _
      rw [Measure.map_fst_prod,
        normalizedFiniteTimeResonanceKernelFiniteMeasure_univ,
        one_smul]

end

end ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability
