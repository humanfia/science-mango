import ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure

/-!
# Finite-time-window Bochner closure for complete potential source slots

The complete canonical potential source-slot observable is jointly
measurable and has an almost-sure bound uniform in time.  Hence it is
Bochner integrable on every fixed compact time window, admits integrable
time sections, and satisfies Fubini.  The unit quadratic and unit quartic
channels are recorded as direct specializations for the history closure.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualPotentialSourceSlotTimeWindowBochner

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The complete potential source-slot observable is jointly measurable with
time as the first product coordinate. -/
theorem measurable_canonicalPotentialSourceSlotObservable_time_sample
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) :
    Measurable fun st : Real × CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (st.2, st.1) := by
  exact (measurable_canonicalPotentialSourceSlotObservable (N := N)
    flowKappa flowBeta flowG hflowBeta a
    sourceKappa sourceBeta sourceG entry block slot).comp
      (measurable_snd.prodMk measurable_fst)

/-- Every complete potential source slot is jointly Bochner integrable on a
fixed symmetric compact time window. -/
theorem integrable_canonicalPotentialSourceSlotObservable_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (st.2, st.1))
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
  let C := canonicalPotentialSourceSlotEnvelope
    (canonicalSignedAmplitudeEnvelope N
      flowKappa flowBeta flowG hflowBeta)
    (canonicalSignedPotentialChannelSourceEnvelope N
      sourceKappa sourceBeta sourceG
      (canonicalWeightedCoordinateEnvelope N
        flowKappa flowBeta flowG hflowBeta)) block slot
  apply Integrable.of_bound
    (measurable_canonicalPotentialSourceSlotObservable_time_sample
      (N := N) flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG entry block slot).aestronglyMeasurable C
  have hboundBase := canonicalPotentialSourceSlotBounds_ae_allTime
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hpositive block slot
  have hboundProduct :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hboundBase
  filter_upwards [hboundProduct] with st hbound
  exact hbound st.1

/-- Unit-quadratic complete source-slot specialization. -/
theorem integrable_canonicalPotentialUnitQuadraticSourceSlot_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1
        entry block slot (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) :=
  integrable_canonicalPotentialSourceSlotObservable_timeWindow
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      1 0 1 entry hpositive block slot window

/-- Unit-quartic complete source-slot specialization. -/
theorem integrable_canonicalPotentialUnitQuarticSourceSlot_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 1 1
        entry block slot (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) :=
  integrable_canonicalPotentialSourceSlotObservable_timeWindow
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      0 1 1 entry hpositive block slot window

/-- Almost every sample has an integrable complete source-slot time section. -/
theorem ae_integrable_time_canonicalPotentialSourceSlotObservable
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry block slot (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalPotentialSourceSlotObservable_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hpositive
      block slot window).prod_left_ae

/-- Fubini for a complete potential source slot on a fixed finite window. -/
theorem integral_canonicalPotentialSourceSlotObservable_swap
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    (∫ time,
      ∫ omega,
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry block slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability
      ∂volume.restrict (Icc (-window) window)) =
      ∫ omega,
        ∫ time,
          canonicalPotentialSourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
            sourceKappa sourceBeta sourceG entry block slot (omega, time)
          ∂volume.restrict (Icc (-window) window)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integral_integral_swap
    (integrable_canonicalPotentialSourceSlotObservable_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hpositive
      block slot window)

end
end ArchonPhysics.CanonicalIIDCoerciveActualPotentialSourceSlotTimeWindowBochner
