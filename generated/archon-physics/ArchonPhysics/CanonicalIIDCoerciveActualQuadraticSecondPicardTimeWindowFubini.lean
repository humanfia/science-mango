import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardSourceTimeWindowBochner

/-!
# Fubini closure for the actual quadratic second-Picard source

The actual source is jointly Bochner integrable on every finite symmetric
time window.  Consequently its annealed expectation is time-integrable, its
time integral is sample-integrable, and the two orders of integration agree.
This remains a fixed finite-volume, finite-time-window statement.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowFubini

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardSourceTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- The annealed actual second-Picard source is Bochner integrable in time on
every finite symmetric window. -/
theorem integrable_expectation_canonicalQuadraticSecondPicardDuhamelSource_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : Prod PhaseSign (OrderedModeIndex N))
    (hentry : Ne entry.2 (lastOrderedIndex (ι := Lattice.Site N)))
    (window : Real) :
    Integrable (fun time : Real =>
      ∫ omega,
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .quadraticSecondPicard (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability)
      (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalQuadraticSecondPicardDuhamelSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hentry window).integral_prod_left

/-- The finite-window time integral of the actual second-Picard source is
Bochner integrable over the canonical sample ensemble. -/
theorem integrable_timeIntegral_canonicalQuadraticSecondPicardDuhamelSource_sample
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : Prod PhaseSign (OrderedModeIndex N))
    (hentry : Ne entry.2 (lastOrderedIndex (ι := Lattice.Site N)))
    (window : Real) :
    Integrable (fun omega : CanonicalSample =>
      ∫ time,
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .quadraticSecondPicard (omega, time)
        ∂volume.restrict (Icc (-window) window))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalQuadraticSecondPicardDuhamelSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hentry window).integral_prod_right

/-- Fubini: annealed expectation and finite-window time integration commute
for the actual quadratic second-Picard source. -/
theorem integral_expectation_canonicalQuadraticSecondPicardDuhamelSource_swap
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : Prod PhaseSign (OrderedModeIndex N))
    (hentry : Ne entry.2 (lastOrderedIndex (ι := Lattice.Site N)))
    (window : Real) :
    (∫ time,
      ∫ omega,
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry .quadraticSecondPicard (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability
      ∂volume.restrict (Icc (-window) window)) =
      ∫ omega,
        ∫ time,
          canonicalQuadraticDuhamelHistorySource (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry .quadraticSecondPicard (omega, time)
          ∂volume.restrict (Icc (-window) window)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integral_integral_swap
    (integrable_canonicalQuadraticSecondPicardDuhamelSource_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hentry window)

end
end ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardTimeWindowFubini
