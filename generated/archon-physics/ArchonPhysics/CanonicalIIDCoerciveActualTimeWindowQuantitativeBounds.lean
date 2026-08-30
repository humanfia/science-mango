import ArchonPhysics.CanonicalIIDCoerciveActualPotentialSourceSlotTimeWindowBochner
import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardSourceTimeWindowBochner
import ArchonPhysics.FiniteSymmetricWindowIntegralBounds

/-!
# Quantitative finite-window bounds for actual canonical sources

The complete potential source slot has a time-independent almost-sure
envelope, so its joint time-sample L1 norm grows at most linearly with the
window length.  The extracted quadratic second-Picard source has the explicit
time-dependent envelope already proved in the history analysis, yielding its
corresponding finite-window estimate.  Neither estimate is uniform as the
window tends to infinity.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualTimeWindowQuantitativeBounds

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualPotentialSourceSlotTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardSourceTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteSymmetricWindowIntegralBounds
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The complete potential source-slot L1 norm is bounded by its uniform
envelope times the exact window length. -/
theorem integral_norm_canonicalPotentialSourceSlotObservable_timeWindow_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I)
    (window : Real) (hwindow : 0 <= window) :
    (∫ st, ‖canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (st.2, st.1)‖
      ∂((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) <=
      canonicalPotentialSourceSlotEnvelope
          (canonicalSignedAmplitudeEnvelope N
            flowKappa flowBeta flowG hflowBeta)
          (canonicalSignedPotentialChannelSourceEnvelope N
            sourceKappa sourceBeta sourceG
            (canonicalWeightedCoordinateEnvelope N
              flowKappa flowBeta flowG hflowBeta)) block slot *
        (2 * window) := by
  let C := canonicalPotentialSourceSlotEnvelope
    (canonicalSignedAmplitudeEnvelope N
      flowKappa flowBeta flowG hflowBeta)
    (canonicalSignedPotentialChannelSourceEnvelope N
      sourceKappa sourceBeta sourceG
      (canonicalWeightedCoordinateEnvelope N
        flowKappa flowBeta flowG hflowBeta)) block slot
  apply integral_norm_timeSample_le_two_mul window hwindow
    (fun st : Real × CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (st.2, st.1)) C
  · exact integrable_canonicalPotentialSourceSlotObservable_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hpositive block slot window
  · have hboundBase := canonicalPotentialSourceSlotBounds_ae_allTime
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        sourceKappa sourceBeta sourceG entry hpositive block slot
    have hboundProduct :=
      (Measure.quasiMeasurePreserving_snd
        (μ := volume.restrict (Icc (-window) window))
        (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hboundBase
    filter_upwards [hboundProduct] with st hbound
    exact hbound st.1

/-- The actual quadratic second-Picard source has the explicit finite-window
L1 bound supplied by its deterministic envelope. -/
theorem integral_norm_canonicalQuadraticSecondPicardDuhamelSource_timeWindow_le
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) (hwindow : 0 <= window) :
    (∫ st, ‖canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .quadraticSecondPicard (st.2, st.1)‖
      ∂((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) <=
      canonicalQuadraticSecondPicardSourceEnvelope N 1 window *
        (2 * window) := by
  apply integral_norm_timeSample_le_two_mul window hwindow
    (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .quadraticSecondPicard (st.2, st.1))
    (canonicalQuadraticSecondPicardSourceEnvelope N 1 window)
  · exact integrable_canonicalQuadraticSecondPicardDuhamelSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hentry window
  · have htimeAE :
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
    filter_upwards [htimeAE, hsimpleAE] with st htime hsimpleSample
    have hsimple : SimpleOrderedSpectrum
        (harmonicHermitian (canonicalMass (N := N) st.2)) := by
      simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian]
        using hsimpleSample
    rw [canonicalQuadraticSecondPicardSource_eq_measurableOrdered
      (N := N) flowKappa flowBeta flowG hflowBeta a st.2 hsimple]
    exact
      (norm_canonicalSignedQuadraticSecondPicardRotatedSource_le
        (N := N) hN ha0 ha1 1 st.2 hsimple entry hentry st.1).trans
        (canonicalQuadraticSecondPicardSourceEnvelope_mono_of_abs_le
          (N := N) 1 st.1 window (by
            simpa [abs_of_nonneg hwindow] using (abs_le.2 htime)))

end
end ArchonPhysics.CanonicalIIDCoerciveActualTimeWindowQuantitativeBounds
