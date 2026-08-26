import ArchonPhysics.RandomMassPositiveLateWindowObservable
import ArchonPhysics.RandomMassReducedPhaseInitialData

/-!
# Canonical random-phase initial data in the positive-mode late-window observable

This module removes the last abstract-initial-data parameter from the
measurable late-window layer.  The initial point is the globally measurable
mass/phase reconstruction with the frozen physical modal-energy profile.
Every theorem remains parametric in a single measurable ambient flow; a later
uniform-shell module identifies that one flow with the genuine uncut reduced
Hamiltonian trajectory almost surely.

No thermalization, kinetic limit, or hitting-time scaling is asserted here.
-/

namespace ArchonPhysics.RandomMassPhaseLateWindowObservable

open ArchonPhysics
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.RandomMassReducedPhaseInitialData

noncomputable section

/-- The canonical iid mass/phase initial point in the common parametric phase
space. -/
def canonicalPhaseInitialSample
    {N : Nat} [NeZero N] (kappa beta g a : Real) :
    RandomEnsemble.SampleSpace → ParametricPhaseSpace N :=
  parametricInitialSample canonicalIIDMassPhaseEnsemble
    (N := N) kappa beta g a

theorem measurable_canonicalPhaseInitialSample
    {N : Nat} [NeZero N] (kappa beta g a : Real) :
    Measurable (canonicalPhaseInitialSample (N := N) kappa beta g a) :=
  measurable_parametricInitialSample canonicalIIDMassPhaseEnsemble
    kappa beta g a

/-- For any one measurable ambient flow, the actual positive-mode
late-window distance of the canonical random initial data is measurable. -/
theorem measurable_canonicalPhaseInitialLateWindowL1Distance
    {N : Nat} [NeZero N] (kappa beta g a : Real)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hflow : Measurable flow) (mu T : Real) :
    Measurable
      (sampledPositiveLateWindowL1Distance
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta g a)
        flow mu T) :=
  canonical_measurable_sampledPositiveLateWindowL1Distance
    (canonicalPhaseInitialSample (N := N) kappa beta g a) flow
    (measurable_canonicalPhaseInitialSample kappa beta g a) hflow mu T

/-- The positive-rational strict-threshold hitting time is a genuine random
variable for the canonical random initial data and any measurable flow. -/
theorem measurable_canonicalPhaseInitialRationalStrictHittingTime
    {N : Nat} [NeZero N] (kappa beta g a : Real)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hflow : Measurable flow) (mu delta : Real) :
    Measurable
      (sampledPositiveLateWindowRationalStrictHittingTime
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta g a)
        flow mu delta) :=
  measurable_sampledPositiveLateWindowRationalStrictHittingTime
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a) flow
    (RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
      canonicalIIDMassPhaseEnsemble)
    (measurable_canonicalPhaseInitialSample kappa beta g a) hflow mu delta

/-- The fixed-duration rational persistence hitting time is measurable for
the same canonical data. -/
theorem measurable_canonicalPhaseInitialRationalPersistentHittingTime
    {N : Nat} [NeZero N] (kappa beta g a : Real)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hflow : Measurable flow) (mu delta duration : Real) :
    Measurable
      (sampledPositiveLateWindowRationalPersistentHittingTime
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta g a)
        flow mu delta duration) :=
  measurable_sampledPositiveLateWindowRationalPersistentHittingTime
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a) flow
    (RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
      canonicalIIDMassPhaseEnsemble)
    (measurable_canonicalPhaseInitialSample kappa beta g a) hflow
    mu delta duration

/-- The same canonical initial datum realizes the frozen ordered physical
modal-energy profile and total harmonic energy one almost surely. -/
theorem canonicalPhaseInitial_exact_profile_ae
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      (∀ k : RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
        RandomMassMeasurableHarmonicEnergy.harmonicOrderedPhysicalModeEnergy
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
            (RandomMassPhaseInitialData.initialPhysicalPosition
              canonicalIIDMassPhaseEnsemble a)
            (RandomMassPhaseInitialData.initialPhysicalMomentum
              canonicalIIDMassPhaseEnsemble a) omega k =
          RandomMassPhaseInitialData.orderedTargetEnergy N a k) ∧
      (∑ k : RandomMassPositiveLateWindowObservable.OrderedModeIndex N,
        RandomMassMeasurableHarmonicEnergy.harmonicOrderedPhysicalModeEnergy
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
            (RandomMassPhaseInitialData.initialPhysicalPosition
              canonicalIIDMassPhaseEnsemble a)
            (RandomMassPhaseInitialData.initialPhysicalMomentum
              canonicalIIDMassPhaseEnsemble a) omega k) = 1 :=
  harmonicOrderedPhysicalModeEnergy_initial_eq_target_ae
    canonicalIIDMassPhaseEnsemble hN ha0 ha1

end

end ArchonPhysics.RandomMassPhaseLateWindowObservable
