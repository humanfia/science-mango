import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowBochner

/-!
# Actual Duhamel-source form of the second-Picard time-window closure

The jointly integrable measurable ordered source is transported back to the
actual Physlib quadratic Duhamel history source on the almost-sure simple
spectrum event.  The time coordinate is kept first so that the result can be
fed directly to the standard product-measure Fubini API.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardSourceTimeWindowBochner

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- The actual quadratic second-Picard Duhamel source is jointly integrable
on every finite symmetric time window. -/
theorem integrable_canonicalQuadraticSecondPicardDuhamelSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : Prod PhaseSign (OrderedModeIndex N))
    (hentry : Ne entry.2 (lastOrderedIndex (ι := Lattice.Site N)))
    (window : Real) :
    Integrable (fun st : Prod Real CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .quadraticSecondPicard (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  have hcanonical :=
    integrable_canonicalSignedQuadraticSecondPicardRotatedSource_timeWindow
      (N := N) hN ha0 ha1 1 entry hentry window
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
  apply canonicalQuadraticSecondPicardSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a st.2
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple

/-- Hence almost every canonical sample has an integrable actual
second-Picard Duhamel source throughout the prescribed finite window. -/
theorem ae_integrable_time_canonicalQuadraticSecondPicardDuhamelSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : Prod PhaseSign (OrderedModeIndex N))
    (hentry : Ne entry.2 (lastOrderedIndex (ι := Lattice.Site N)))
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .quadraticSecondPicard (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalQuadraticSecondPicardDuhamelSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hentry window).prod_left_ae

end
end ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardSourceTimeWindowBochner
