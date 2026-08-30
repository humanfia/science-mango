import ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareHistoryIntegrability
import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability

/-!
# Compact-time Bochner closure for the actual defect-square primitive

The ordered signed representative of the quadratic defect-square history is
jointly measurable in time and canonical sample. Its conserved-energy
envelope is independent of time, hence it is integrable on every fixed compact
time window. The actual Physlib history is recovered almost everywhere on the
simple-spectrum event. No window-uniform or kinetic-scale assertion is made.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareTimeWindowBochner

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

local instance canonicalProbabilityFiniteMeasure :
    IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩

theorem measurable_canonicalOrderedHistoryDefect_prod
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (k : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedHistoryDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a st.2 st.1 k := by
  unfold canonicalOrderedHistoryDefect
  exact
    (measurable_canonicalOrderedModalPosition (N := N)
      flowKappa flowBeta flowG hflowBeta a k).sub
    (measurable_canonicalOrderedFreeCoordinate_prod (N := N) a k)

theorem measurable_canonicalOrderedDefectSquareTensorSource_prod
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (observed : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedDefectSquareTensorSource (N := N)
        flowKappa flowBeta flowG hflowBeta a observed st.2 st.1 := by
  unfold canonicalOrderedDefectSquareTensorSource
  apply Finset.measurable_sum
  intro modes _hmodes
  apply
    (Complex.measurable_ofReal.comp
      ((measurable_canonicalOrderedSignedInteractionTensor (N := N) 3
        (Fin.cons observed (fun r =>
          (orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))).comp
            measurable_fst)).mul
  apply Finset.measurable_prod
  intro r _hr
  exact Complex.measurable_ofReal.comp
    (measurable_canonicalOrderedHistoryDefect_prod (N := N)
      flowKappa flowBeta flowG hflowBeta a
        ((orderedIndexEquiv (ι := Lattice.Site N)).symm (modes r)))

theorem measurable_canonicalOrderedDefectSquareRotatedSource_prod
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (observed : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a observed st.2 st.1 := by
  unfold canonicalOrderedDefectSquareRotatedSource
    forcedModeSource phaseFactor
  have hfrequency : Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFrequency (N := N) observed st.1 :=
    (measurable_canonicalOrderedFrequency (N := N) observed).comp
      measurable_fst
  have htensor :=
    measurable_canonicalOrderedDefectSquareTensorSource_prod
      (N := N) flowKappa flowBeta flowG hflowBeta a observed
  fun_prop

theorem measurable_canonicalSignedDefectSquareRotatedSource_prod
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      canonicalSignedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a entry st.2 st.1 := by
  rcases entry with ⟨sign, observed⟩
  cases sign with
  | phase =>
      exact measurable_canonicalOrderedDefectSquareRotatedSource_prod
        (N := N) flowKappa flowBeta flowG hflowBeta a observed
  | conjugate =>
      exact Complex.continuous_conj.measurable.comp
        (measurable_canonicalOrderedDefectSquareRotatedSource_prod
          (N := N) flowKappa flowBeta flowG hflowBeta a observed)

theorem measurable_canonicalSignedDefectSquareRotatedSource_time_sample
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :
    Measurable fun st : Real × CanonicalSample =>
      canonicalSignedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a entry st.1 st.2 := by
  change Measurable
    ((fun st : CanonicalSample × Real =>
      canonicalSignedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a entry st.2 st.1) ∘
      fun st : Real × CanonicalSample => (st.2, st.1))
  exact
    (measurable_canonicalSignedDefectSquareRotatedSource_prod
      (N := N) flowKappa flowBeta flowG hflowBeta a entry).comp
      (measurable_snd.prodMk measurable_fst)
theorem integrable_canonicalSignedDefectSquareRotatedSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalSignedDefectSquareRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a entry st.1 st.2)
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  let _ : IsFiniteMeasure (volume.restrict (Icc (-window) window)) := by
    infer_instance
  let _ : IsFiniteMeasure
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
    infer_instance
  apply Integrable.of_bound
    (measurable_canonicalSignedDefectSquareRotatedSource_time_sample
      (N := N) flowKappa flowBeta flowG hflowBeta a entry).aestronglyMeasurable
    (canonicalDefectSquareSourceEnvelope N C flowKappa flowBeta G)
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble (by omega)
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  apply norm_canonicalSignedDefectSquareRotatedSource_le
    (N := N) hN ha0 ha1 C hC hPoincare
      flowKappa flowBeta flowG G hflowBeta hG hg st.2
  · simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
  · exact hentry

theorem integrable_canonicalQuadraticDefectSquareSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .defectSquare (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  have hcanonical :=
    integrable_canonicalSignedDefectSquareRotatedSource_timeWindow
      (N := N) hN ha0 ha1 C hC hPoincare
        flowKappa flowBeta flowG G hflowBeta hG hg entry hentry window
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
  apply canonicalQuadraticDefectSquareSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a st.2
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple
theorem aestronglyMeasurable_canonicalQuadraticDefectSquareSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    AEStronglyMeasurable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .defectSquare (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) :=
  (integrable_canonicalQuadraticDefectSquareSource_timeWindow
    (N := N) hN ha0 ha1 C hC hPoincare
      flowKappa flowBeta flowG G hflowBeta hG hg entry hentry window).1

theorem ae_integrable_time_canonicalQuadraticDefectSquareSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .defectSquare (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  exact
    (integrable_canonicalQuadraticDefectSquareSource_timeWindow
      (N := N) hN ha0 ha1 C hC hPoincare
        flowKappa flowBeta flowG G hflowBeta hG hg
          entry hentry window).prod_left_ae

theorem integrable_timeIntegral_canonicalQuadraticDefectSquareSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    Integrable (fun omega : CanonicalSample =>
      ∫ time : Real,
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .defectSquare (omega, time)
        ∂(volume.restrict (Icc (-window) window)))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact
    (integrable_canonicalQuadraticDefectSquareSource_timeWindow
      (N := N) hN ha0 ha1 C hC hPoincare
        flowKappa flowBeta flowG G hflowBeta hG hg
          entry hentry window).integral_prod_right

theorem integral_canonicalQuadraticDefectSquareSource_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .defectSquare (st.2, st.1)
      ∂((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalQuadraticDuhamelHistorySource (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry .defectSquare (omega, time)
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  exact integral_prod_symm _
    (integrable_canonicalQuadraticDefectSquareSource_timeWindow
      (N := N) hN ha0 ha1 C hC hPoincare
        flowKappa flowBeta flowG G hflowBeta hG hg
          entry hentry window)

end
end ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareTimeWindowBochner
