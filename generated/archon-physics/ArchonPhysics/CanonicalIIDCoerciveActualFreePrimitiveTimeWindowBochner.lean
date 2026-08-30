import ArchonPhysics.CanonicalIIDCoerciveActualFreeCubicHistoryIntegrability
import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability

/-!
# Compact-time Bochner closure for actual free primitive sources

The globally measurable ordered representatives are controlled on every fixed
compact time window. They agree almost everywhere with the actual Physlib
histories. No kinetic-time uniformity is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualFreePrimitiveTimeWindowBochner

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualFreeCubicHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

local instance canonicalProbabilityFiniteMeasure :
    IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩

variable {N : Nat} [NeZero N]

theorem measurable_canonicalSignedFreeQuadraticRotatedSource_prod
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry st.2 st.1 := by
  rcases entry with ⟨sign, observed⟩
  cases sign with
  | phase =>
      exact measurable_canonicalOrderedFreeQuadraticRotatedSource_prod
        (N := N) a observed
  | conjugate =>
      exact Complex.continuous_conj.measurable.comp
        (measurable_canonicalOrderedFreeQuadraticRotatedSource_prod
          (N := N) a observed)

theorem measurable_canonicalSignedFreeQuadraticRotatedSource_time_sample
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :
    Measurable fun st : Real × CanonicalSample =>
      canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry st.1 st.2 := by
  change Measurable
    ((fun st : CanonicalSample × Real =>
      canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry st.2 st.1) ∘
      fun st : Real × CanonicalSample => (st.2, st.1))
  exact (measurable_canonicalSignedFreeQuadraticRotatedSource_prod
    (N := N) a entry).comp (measurable_snd.prodMk measurable_fst)



theorem measurable_canonicalOrderedFreeCubicTensorSource_prod
    (a : Real) (observed : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFreeCubicTensorSource (N := N)
        a observed st.2 st.1 := by
  unfold canonicalOrderedFreeCubicTensorSource
  apply Finset.measurable_sum
  intro modes _hmodes
  apply
    ((measurable_canonicalOrderedSignedInteractionTensor (N := N) 4
      (Fin.cons observed (fun r =>
        (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))).comp
          measurable_fst).mul
  apply Finset.measurable_prod
  intro r _hr
  exact measurable_canonicalOrderedFreeCoordinate_prod (N := N) a
    ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r))

theorem measurable_canonicalOrderedFreeCubicRotatedSource_prod
    (a : Real) (observed : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFreeCubicRotatedSource (N := N)
        a observed st.2 st.1 := by
  unfold canonicalOrderedFreeCubicRotatedSource forcedModeSource phaseFactor
  have hfrequency : Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFrequency (N := N) observed st.1 :=
    (measurable_canonicalOrderedFrequency (N := N) observed).comp
      measurable_fst
  have htensor :=
    measurable_canonicalOrderedFreeCubicTensorSource_prod
      (N := N) a observed
  fun_prop

theorem measurable_canonicalSignedFreeCubicRotatedSource_prod
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalSignedFreeCubicRotatedSource (N := N)
        a entry st.2 st.1 := by
  rcases entry with ⟨sign, observed⟩
  cases sign with
  | phase =>
      exact measurable_canonicalOrderedFreeCubicRotatedSource_prod
        (N := N) a observed
  | conjugate =>
      exact Complex.continuous_conj.measurable.comp
        (measurable_canonicalOrderedFreeCubicRotatedSource_prod
          (N := N) a observed)

theorem measurable_canonicalSignedFreeCubicRotatedSource_time_sample
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :
    Measurable fun st : Real × CanonicalSample =>
      canonicalSignedFreeCubicRotatedSource (N := N)
        a entry st.1 st.2 := by
  change Measurable
    ((fun st : CanonicalSample × Real =>
      canonicalSignedFreeCubicRotatedSource (N := N)
        a entry st.2 st.1) ∘
      fun st : Real × CanonicalSample => (st.2, st.1))
  exact (measurable_canonicalSignedFreeCubicRotatedSource_prod
    (N := N) a entry).comp (measurable_snd.prodMk measurable_fst)

theorem integrable_canonicalSignedFreeQuadraticRotatedSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry st.1 st.2)
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  let _ : IsFiniteMeasure (volume.restrict (Icc (-window) window)) := by
    infer_instance
  let _ : IsFiniteMeasure
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
    infer_instance
  apply Integrable.of_bound
    (measurable_canonicalSignedFreeQuadraticRotatedSource_time_sample
      (N := N) a entry).aestronglyMeasurable
    (canonicalFreeQuadraticSourceEnvelope N)
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble (by omega)
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  apply norm_canonicalSignedFreeQuadraticRotatedSource_le
    (N := N) hN ha0 ha1 st.2
  · simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
  · exact hentry

theorem integrable_canonicalSignedFreeCubicRotatedSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalSignedFreeCubicRotatedSource (N := N)
        a entry st.1 st.2)
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  let _ : IsFiniteMeasure (volume.restrict (Icc (-window) window)) := by
    infer_instance
  let _ : IsFiniteMeasure
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
    infer_instance
  apply Integrable.of_bound
    (measurable_canonicalSignedFreeCubicRotatedSource_time_sample
      (N := N) a entry).aestronglyMeasurable
    (canonicalFreeCubicSourceEnvelope N)
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble (by omega)
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  apply norm_canonicalSignedFreeCubicRotatedSource_le
    (N := N) hN ha0 ha1 st.2
  · simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
  · exact hentry
theorem ae_integrable_time_canonicalSignedFreeQuadraticRotatedSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalSignedFreeQuadraticRotatedSource (N := N)
          a entry time omega)
        (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalSignedFreeQuadraticRotatedSource_timeWindow
      (N := N) hN ha0 ha1 entry hentry window).prod_left_ae

theorem ae_integrable_time_canonicalSignedFreeCubicRotatedSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalSignedFreeCubicRotatedSource (N := N)
          a entry time omega)
        (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalSignedFreeCubicRotatedSource_timeWindow
      (N := N) hN ha0 ha1 entry hentry window).prod_left_ae

theorem integrable_timeIntegral_canonicalSignedFreeQuadraticRotatedSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun omega : CanonicalSample =>
      ∫ time : Real,
        canonicalSignedFreeQuadraticRotatedSource (N := N)
          a entry time omega
        ∂(volume.restrict (Icc (-window) window)))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalSignedFreeQuadraticRotatedSource_timeWindow
      (N := N) hN ha0 ha1 entry hentry window).integral_prod_right

theorem integrable_timeIntegral_canonicalSignedFreeCubicRotatedSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun omega : CanonicalSample =>
      ∫ time : Real,
        canonicalSignedFreeCubicRotatedSource (N := N)
          a entry time omega
        ∂(volume.restrict (Icc (-window) window)))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalSignedFreeCubicRotatedSource_timeWindow
      (N := N) hN ha0 ha1 entry hentry window).integral_prod_right

theorem integral_canonicalSignedFreeQuadraticRotatedSource_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalSignedFreeQuadraticRotatedSource (N := N)
        a entry st.1 st.2
      ∂((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalSignedFreeQuadraticRotatedSource (N := N)
            a entry time omega
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integral_prod_symm _
    (integrable_canonicalSignedFreeQuadraticRotatedSource_timeWindow
      (N := N) hN ha0 ha1 entry hentry window)

theorem integral_canonicalSignedFreeCubicRotatedSource_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalSignedFreeCubicRotatedSource (N := N)
        a entry st.1 st.2
      ∂((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalSignedFreeCubicRotatedSource (N := N)
            a entry time omega
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integral_prod_symm _
    (integrable_canonicalSignedFreeCubicRotatedSource_timeWindow
      (N := N) hN ha0 ha1 entry hentry window)
theorem integrable_canonicalQuadraticFreeFirstPicardSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .freeFirstPicard (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  have hcanonical :=
    integrable_canonicalSignedFreeQuadraticRotatedSource_timeWindow
      (N := N) hN ha0 ha1 entry hentry window
  refine hcanonical.congr ?_
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble (by omega)
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  symm
  apply canonicalQuadraticFreeFirstPicardSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a st.2
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple

theorem integrable_canonicalQuarticFreeCubicSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .freeCubicSecondPicard (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  have hcanonical :=
    integrable_canonicalSignedFreeCubicRotatedSource_timeWindow
      (N := N) hN ha0 ha1 entry hentry window
  refine hcanonical.congr ?_
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble (by omega)
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  symm
  apply canonicalQuarticFreeCubicSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a st.2
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
theorem ae_integrable_time_canonicalQuadraticFreeFirstPicardSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .freeFirstPicard (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  exact
    (integrable_canonicalQuadraticFreeFirstPicardSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hentry window).prod_left_ae

theorem ae_integrable_time_canonicalQuarticFreeCubicSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalQuarticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .freeCubicSecondPicard (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  exact
    (integrable_canonicalQuarticFreeCubicSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hentry window).prod_left_ae

theorem integrable_timeIntegral_canonicalQuadraticFreeFirstPicardSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun omega : CanonicalSample =>
      ∫ time : Real,
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .freeFirstPicard (omega, time)
        ∂(volume.restrict (Icc (-window) window)))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact
    (integrable_canonicalQuadraticFreeFirstPicardSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hentry window).integral_prod_right

theorem integrable_timeIntegral_canonicalQuarticFreeCubicSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun omega : CanonicalSample =>
      ∫ time : Real,
        canonicalQuarticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .freeCubicSecondPicard (omega, time)
        ∂(volume.restrict (Icc (-window) window)))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact
    (integrable_canonicalQuarticFreeCubicSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hentry window).integral_prod_right

theorem integral_canonicalQuadraticFreeFirstPicardSource_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .freeFirstPicard (st.2, st.1)
      ∂((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalQuadraticDuhamelHistorySource (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry .freeFirstPicard (omega, time)
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  exact integral_prod_symm _
    (integrable_canonicalQuadraticFreeFirstPicardSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hentry window)

theorem integral_canonicalQuarticFreeCubicSource_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .freeCubicSecondPicard (st.2, st.1)
      ∂((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalQuarticDuhamelHistorySource (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry .freeCubicSecondPicard (omega, time)
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  exact integral_prod_symm _
    (integrable_canonicalQuarticFreeCubicSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hentry window)

end
end ArchonPhysics.CanonicalIIDCoerciveActualFreePrimitiveTimeWindowBochner
