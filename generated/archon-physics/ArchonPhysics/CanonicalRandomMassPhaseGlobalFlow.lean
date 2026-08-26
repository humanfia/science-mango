import ArchonPhysics.CanonicalRandomMassGlobalFlow
import ArchonPhysics.RandomMassInitialEnergyBound

/-!
# Canonical global flow for the frozen random-mass random-phase initial state

The normalized frozen modal profile has the sample-independent nonlinear
energy ceiling `initialEnergyUpperBound kappa beta g`.  Feeding that exact
ceiling into `CanonicalRandomMassGlobalFlow` removes the last sample-dependent
parameter from the global continuation construction.

For fixed `N`, couplings, and the coercivity proof, the resulting canonical
cutoff flow is independent of the probability space, mass realization, Haar
phases, and profile parameter `a`.  Every allowed random initial sample is fed
into this same flow.  The random trajectory is jointly measurable in sample
and time; almost surely, simple spectrum and the uniform energy theorem identify
it for every time with an embedded genuine untruncated reduced Hamiltonian
trajectory.

No kinetic-limit or thermalization conclusion is made here.
-/

namespace ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassInitialEnergyBound
open ArchonPhysics.RandomMassReducedPhaseInitialData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- The canonical iid shell instantiated with the proved common nonlinear
initial-energy ceiling. -/
def canonicalRandomMassPhaseEnergyShell
    (N : Nat) [NeZero N] (kappa beta g : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    UniformRandomMassEnergyShell N :=
  canonicalIIDUniformEnergyShell N kappa beta g
    (initialEnergyUpperBound kappa beta g) hbeta

/-- One sample-independent canonical cutoff flow for the complete frozen
random-mass/random-phase initial ensemble. -/
def canonicalRandomMassPhaseGlobalFlow
    (N : Nat) [NeZero N] (kappa beta g : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ParametricPhaseSpace N × Real → ParametricPhaseSpace N :=
  canonicalIIDRandomMassGlobalFlow N kappa beta g
    (initialEnergyUpperBound kappa beta g) hbeta

theorem measurable_canonicalRandomMassPhaseGlobalFlow
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    Measurable
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta) :=
  measurable_canonicalIIDRandomMassGlobalFlow
    kappa beta g (initialEnergyUpperBound kappa beta g) hbeta

@[simp] theorem canonicalRandomMassPhaseGlobalFlow_zero
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (x : ParametricPhaseSpace N) :
    canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta (x, 0) = x := by
  exact canonicalRandomMassGlobalFlow_zero
    (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta) x

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Every frozen random-phase initial point is evolved by the same canonical
flow.  The profile parameter changes only the initial point, never the flow. -/
def canonicalRandomMassPhaseTrajectory
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) : Omega × Real → ParametricPhaseSpace N :=
  canonicalIIDRandomMassTrajectory ensemble kappa beta g
    (initialEnergyUpperBound kappa beta g) hbeta a

/-- Joint measurability in the random mass/phase sample and physical time. -/
theorem measurable_canonicalRandomMassPhaseTrajectory
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) :
    Measurable
      (canonicalRandomMassPhaseTrajectory (N := N)
        ensemble kappa beta g hbeta a) :=
  measurable_canonicalIIDRandomMassTrajectory ensemble kappa beta g
    (initialEnergyUpperBound kappa beta g) hbeta a

/-- Every sample path of the canonical random trajectory is continuous.  This
holds even on the null degenerate-spectrum locus because the totalized initial
sample is evolved by the same smooth cutoff flow. -/
theorem continuous_canonicalRandomMassPhaseTrajectory_path
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : Omega) :
    Continuous (fun t => canonicalRandomMassPhaseTrajectory (N := N)
      ensemble kappa beta g hbeta a (omega, t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (CanonicalGlobalMeasurableFlow.canonicalCutoffFlow_hasDerivAt
    parameterizedHamiltonVectorField
    parameterizedHamiltonVectorField_contDiff
    (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius
    (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius_nonneg
    (parametricInitialSample ensemble (N := N) kappa beta g a omega) t).continuousAt

@[simp] theorem canonicalRandomMassPhaseTrajectory_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : Omega) :
    canonicalRandomMassPhaseTrajectory (N := N)
        ensemble kappa beta g hbeta a (omega, 0) =
      parametricInitialSample ensemble (N := N) kappa beta g a omega := by
  exact canonicalIIDRandomMassTrajectory_zero ensemble kappa beta g
    (initialEnergyUpperBound kappa beta g) hbeta a omega

/-- Pointwise identification on the simple-spectrum locus.  The required
energy estimate is discharged internally by `RandomMassInitialEnergyBound`. -/
theorem canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    ∃ z : Real → ReducedPhaseSpace
        (ensemble.restrictPositiveMass (N := N) omega),
      z 0 = reducedInitialStateOfSimple ensemble a omega hsimple ∧
      (∀ t, HasDerivAt z
        (reducedVectorField (ensemble.restrictPositiveMass (N := N) omega)
          kappa beta g (z t)) t) ∧
      (∀ t, canonicalRandomMassPhaseTrajectory (N := N) ensemble
          kappa beta g hbeta a (omega, t) =
        embedReducedPoint (ensemble.restrictPositiveMass (N := N) omega)
          kappa beta g (z t)) ∧
      ∀ t, reducedHamiltonian
        (ensemble.restrictPositiveMass (N := N) omega) kappa beta g (z t) =
        reducedHamiltonian (ensemble.restrictPositiveMass (N := N) omega)
          kappa beta g
            (reducedInitialStateOfSimple ensemble a omega hsimple) := by
  apply canonicalIIDRandomMassTrajectory_matches_reduced_of_energy_le
    ensemble kappa beta g (initialEnergyUpperBound kappa beta g)
      hbeta a omega hsimple
  exact reducedHamiltonian_reducedInitialStateOfSimple_le
    ensemble hN ha0 ha1 hbeta g omega hsimple

/-- Almost surely, the one measurable random trajectory is a genuine
untruncated reduced Hamiltonian trajectory for every real time.  The
simple-spectrum proof is packaged existentially because the reduced initial
state is a mass-dependent subtype. -/
theorem canonicalRandomMassPhaseTrajectory_matches_reduced_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ∀ᵐ omega ∂ensemble.probability,
      ∃ hsimple : SimpleOrderedSpectrum
          (harmonicHermitian
            (ensemble.restrictPositiveMass (N := N) omega)),
        ∃ z : Real → ReducedPhaseSpace
            (ensemble.restrictPositiveMass (N := N) omega),
          z 0 = reducedInitialStateOfSimple ensemble a omega hsimple ∧
          (∀ t, HasDerivAt z
            (reducedVectorField
              (ensemble.restrictPositiveMass (N := N) omega)
              kappa beta g (z t)) t) ∧
          (∀ t, canonicalRandomMassPhaseTrajectory (N := N) ensemble
              kappa beta g hbeta a (omega, t) =
            embedReducedPoint
              (ensemble.restrictPositiveMass (N := N) omega)
              kappa beta g (z t)) ∧
          ∀ t, reducedHamiltonian
            (ensemble.restrictPositiveMass (N := N) omega)
              kappa beta g (z t) =
            reducedHamiltonian
              (ensemble.restrictPositiveMass (N := N) omega)
              kappa beta g
                (reducedInitialStateOfSimple ensemble a omega hsimple) := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) ensemble (show 2 ≤ N by omega)
  filter_upwards [hsimpleAE] with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian] using hsimpleSample
  exact ⟨hsimple,
    canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
      ensemble hN ha0 ha1 kappa beta g hbeta omega hsimple⟩

end

end ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
