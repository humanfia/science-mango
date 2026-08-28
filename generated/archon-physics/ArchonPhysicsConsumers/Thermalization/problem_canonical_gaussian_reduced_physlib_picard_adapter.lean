import ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
import ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
import ArchonPhysics.CanonicalRandomMassGlobalFlow
import ArchonPhysics.TruncatedGaussianMassPhaseEnsemble

/-!
# Canonical Gaussian reduced trajectory as a Physlib Picard consumer

For one frozen conditioned-Gaussian mass sample and one reduced initial
state, the existing canonical common-shell flow supplies a genuine reduced
global trajectory.  The deterministic adapter turns that trajectory into
Physlib `Time` paths and the microscopic post-second-Picard estimate is then
applied without externally supplied `p` or `q`.
-/

namespace ArchonPhysicsConsumers.Thermalization.CanonicalGaussianReducedPhyslibPicardAdapter

open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
open ArchonPhysics.TruncatedGaussianMassLaw
open ArchonPhysics.GaussianIIDMassPhaseEnsemble

noncomputable section

def canonicalGaussianSampleMass
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) :
    Lattice.PositiveMassConfig N :=
  ensemble.restrictPositiveMass sample

/-- Gaussian support gives admissibility for the same canonical common shell
used by the iid random-mass global flow. -/
theorem gaussianSample_massAdmissible_canonicalIIDUniformEnergyShell
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (kappa beta g H : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : Omega) :
    (canonicalIIDUniformEnergyShell N kappa beta g H hbeta).MassAdmissible
      (canonicalGaussianSampleMass ensemble sample) := by
  intro i
  have hs := ensemble.mass_mem_support i.val sample
  have hmpos := (canonicalGaussianSampleMass ensemble sample).mass_pos i
  exact ⟨hs.1, hs.2,
    (inv_le_inv₀ randomMassUpper_pos hmpos).2 hs.2,
    (inv_le_inv₀ hmpos RandomEnsemble.massLower_pos).2 hs.1⟩

/-- Norm of the exact interaction-picture error after lifting a reduced
trajectory to Physlib. -/
def liftedReducedSecondPicardError
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (observed : Lattice.Site N)
    (z : Real → ReducedPhaseSpace m)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (T : Real) : Real :=
  ‖phaseRenormalize (modeFrequency m observed * T)
        (physlibModeAmplitude m observed
          (physlibMomentumPathOfReducedTrajectory z)
          (physlibPositionPathOfReducedTrajectory z) T) -
      twoStepPerturbedAmplitude g
        (physlibModeAmplitude m observed
          (physlibMomentumPathOfReducedTrajectory z)
          (physlibPositionPathOfReducedTrajectory z) 0)
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase T observed)
        (physlibFPUTSecondPicardCoefficient
          m kappa beta observed radius phase T)‖

/-- A canonical global reduced trajectory exists for the frozen Gaussian
sample, agrees with the already-selected common-shell flow, lifts to a genuine
Physlib Hamilton solution, and obeys the explicit high-Picard energy bound.
No external physical paths or solution certificate are inputs. -/
theorem exists_canonicalGaussianReducedTrajectory_with_physlibPicardErrorBound
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    {kappa beta g H T : Real}
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (z0 : ReducedPhaseSpace (canonicalGaussianSampleMass ensemble sample))
    (henergy0 : reducedHamiltonian
      (canonicalGaussianSampleMass ensemble sample) kappa beta g z0 ≤ H)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (homega : 0 < modeFrequency
      (canonicalGaussianSampleMass ensemble sample) observed)
    (hT : 0 ≤ T) :
    ∃ z : Real →
        ReducedPhaseSpace (canonicalGaussianSampleMass ensemble sample),
      z 0 = z0 ∧
      (∀ time, HasDerivAt z
        (reducedVectorField (canonicalGaussianSampleMass ensemble sample)
          kappa beta g (z time)) time) ∧
      (∀ time,
        canonicalIIDRandomMassGlobalFlow N kappa beta g H hbeta
            (embedReducedPoint (canonicalGaussianSampleMass ensemble sample)
              kappa beta g z0, time) =
          embedReducedPoint (canonicalGaussianSampleMass ensemble sample)
            kappa beta g (z time)) ∧
      Differentiable Real (physlibMomentumPathOfReducedTrajectory z) ∧
      Differentiable Real (physlibPositionPathOfReducedTrajectory z) ∧
      SatisfiesHamiltonEquations
        (canonicalGaussianSampleMass ensemble sample) kappa beta g
        (physlibMomentumPathOfReducedTrajectory z)
        (physlibPositionPathOfReducedTrajectory z) ∧
      liftedReducedSecondPicardError
          (canonicalGaussianSampleMass ensemble sample)
          kappa beta g observed z radius phase T ≤
        afterSecondPicardWindowEnvelope
          (canonicalGaussianSampleMass ensemble sample)
          kappa beta g observed
          (actualModalEnergyL1Envelope N (6 / 5 : Real) kappa beta H)
          radius T * T := by
  let m : Lattice.PositiveMassConfig N :=
    canonicalGaussianSampleMass ensemble sample
  let shell := canonicalIIDUniformEnergyShell N kappa beta g H hbeta
  have hmass : shell.MassAdmissible m := by
    simpa [shell, m] using
      gaussianSample_massAdmissible_canonicalIIDUniformEnergyShell
        ensemble kappa beta g H hbeta sample
  obtain ⟨z, hz0, hz, hmatch, _hflowBound, _hflowDeriv,
      henergyConserved, _hjoint⟩ :=
    canonicalRandomMassGlobalFlow_matches_reduced
      shell m hmass z0 henergy0
  have hp := differentiable_physlibMomentumPathOfReducedTrajectory
    m kappa beta g z hz
  have hq := differentiable_physlibPositionPathOfReducedTrajectory
    m kappa beta g z hz
  have hHamilton :=
    satisfiesHamiltonEquations_physlibPathsOfReducedTrajectory
      m kappa beta g z hz
  have hmassUpper : ∀ i : Lattice.Site N, m.mass i ≤ (6 / 5 : Real) := by
    intro i
    simpa [m, canonicalGaussianSampleMass, RandomEnsemble.massUpper] using
      (ensemble.mass_mem_support i.val sample).2
  have hgauge : ∀ time ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration
        (realReparametrize
          (physlibPositionPathOfReducedTrajectory z) time) i = 0 := by
    intro time htime
    exact massGauge_realReparametrize_physlibPositionPath m z time
  have henergyConserved' : ∀ time,
      reducedHamiltonian m kappa beta g (z time) =
        reducedHamiltonian m kappa beta g z0 := by
    intro time
    simpa [shell, canonicalIIDUniformEnergyShell] using
      henergyConserved time
  have henergy : ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration
          (realReparametrize
            (physlibMomentumPathOfReducedTrajectory z) time))
        (asConfiguration
          (realReparametrize
            (physlibPositionPathOfReducedTrajectory z) time)) ≤ H := by
    intro time htime
    rw [hamiltonian_realReparametrize_physlibPaths_eq_reducedHamiltonian,
      henergyConserved' time]
    simpa [m] using henergy0
  have herror :=
    norm_interactionPicture_physlibMode_sub_twoStep_le_energyWindow
      m (mUpper := (6 / 5 : Real))
      (kappa := kappa) (beta := beta) (g := g) (H := H) (T := T)
      (by norm_num) hmassUpper hbeta observed
      (physlibMomentumPathOfReducedTrajectory z)
      (physlibPositionPathOfReducedTrajectory z)
      hp hq hHamilton radius phase homega hT hgauge henergy
  refine ⟨z, hz0, hz, ?_, hp, hq, hHamilton, ?_⟩
  · intro time
    simpa [canonicalIIDRandomMassGlobalFlow, canonicalIIDUniformEnergyShell,
      shell, m] using hmatch time
  · simpa [liftedReducedSecondPicardError, m] using herror

#print axioms gaussianSample_massAdmissible_canonicalIIDUniformEnergyShell
#print axioms exists_canonicalGaussianReducedTrajectory_with_physlibPicardErrorBound

end

end ArchonPhysicsConsumers.Thermalization.CanonicalGaussianReducedPhyslibPicardAdapter
