import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowIntegrability

/-!
# Bochner closure on a compact time window

This module combines joint measurability, the deterministic second-Picard
envelope, and almost-sure simplicity of the canonical random-mass spectrum.
The result is genuine product-space integrability on every fixed compact time
window.  In particular, Fubini may be used without adding a hidden
time-dependent integrability assumption.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowBochner

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowIntegrability
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- The fixed-time source envelope is monotone when the absolute time is
enlarged. -/
theorem canonicalQuadraticSecondPicardSourceEnvelope_mono_of_abs_le
    (kappa time window : Real) (htime : |time| <= |window|) :
    canonicalQuadraticSecondPicardSourceEnvelope N kappa time <=
      canonicalQuadraticSecondPicardSourceEnvelope N kappa window := by
  unfold canonicalQuadraticSecondPicardSourceEnvelope
  have hnormalization :
      0 <= canonicalPositiveFrequencyNormalizationEnvelope N :=
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg (N := N)
  have hrow : 0 <= canonicalFreeQuadraticTensorRowEnvelope N := by
    unfold canonicalFreeQuadraticTensorRowEnvelope
    positivity
  have hradius : 0 <= canonicalFreeRadiusL1Envelope N := by
    unfold canonicalFreeRadiusL1Envelope
    positivity
  have hrate : 0 <= canonicalFirstPicardModalL1RateEnvelope N kappa := by
    unfold canonicalFirstPicardModalL1RateEnvelope
    positivity
  have hcoefficient :
      0 <= canonicalPositiveFrequencyNormalizationEnvelope N *
        (|kappa| *
          (2 * canonicalFreeQuadraticTensorRowEnvelope N *
            canonicalFreeRadiusL1Envelope N *
            canonicalFirstPicardModalL1RateEnvelope N kappa)) :=
    mul_nonneg hnormalization
      (mul_nonneg (abs_nonneg kappa)
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hrow) hradius) hrate))
  have hmul := mul_le_mul_of_nonneg_left htime hcoefficient
  simpa only [mul_assoc] using hmul

/-- The actual measurable ordered second-Picard source is Bochner integrable
jointly in time and in the canonical sample on every compact symmetric time
window. -/
theorem integrable_canonicalSignedQuadraticSecondPicardRotatedSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa : Real) (entry : Prod PhaseSign (OrderedModeIndex N))
    (hentry : Ne entry.2 (lastOrderedIndex (ι := Lattice.Site N)))
    (window : Real) :
    Integrable (fun st : Prod Real CanonicalSample =>
      canonicalSignedQuadraticSecondPicardRotatedSource (N := N)
        kappa a entry st.1 st.2)
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
    (measurable_canonicalSignedQuadraticSecondPicardRotatedSource_time_sample
      (N := N) kappa a entry).aestronglyMeasurable
    (canonicalQuadraticSecondPicardSourceEnvelope N kappa window)
  have htimeAE :
      ∀ᵐ st ∂((volume.restrict (Icc (-window) window)).prod
          canonicalIIDMassPhaseEnsemble.probability),
        st.1 ∈ Icc (-window) window :=
    (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae
        (ae_restrict_mem measurableSet_Icc)
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble (by omega)
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [htimeAE, hsimpleAE] with st htime hsimple
  have hsimple' :
      SimpleOrderedSpectrum
        (harmonicHermitian (canonicalMass (N := N) st.2)) := by
    simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
  exact
    (norm_canonicalSignedQuadraticSecondPicardRotatedSource_le
      (N := N) hN ha0 ha1 kappa st.2 hsimple' entry hentry st.1).trans
      (canonicalQuadraticSecondPicardSourceEnvelope_mono_of_abs_le
        (N := N) kappa st.1 window (((abs_le).2 htime).trans (le_abs_self window)))

/-- For almost every canonical sample, the complete second-Picard source is
integrable in time on the selected finite window. -/
theorem ae_integrable_time_canonicalSignedQuadraticSecondPicardRotatedSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa : Real) (entry : Prod PhaseSign (OrderedModeIndex N))
    (hentry : Ne entry.2 (lastOrderedIndex (ι := Lattice.Site N)))
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalSignedQuadraticSecondPicardRotatedSource (N := N)
          kappa a entry time omega)
        (volume.restrict (Icc (-window) window)) :=
  by
    let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
      ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
    exact
      (integrable_canonicalSignedQuadraticSecondPicardRotatedSource_timeWindow
        (N := N) hN ha0 ha1 kappa entry hentry window).prod_left_ae

end
end ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowBochner
