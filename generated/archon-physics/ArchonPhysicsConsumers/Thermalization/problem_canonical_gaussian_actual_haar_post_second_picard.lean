import ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
import ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
import ArchonPhysics.CanonicalRandomMassGlobalFlow
import ArchonPhysics.TruncatedGaussianMassPhaseEnsemble

/-!
# Consumer: canonical Gaussian trajectory with exact Haar matched charges

For one frozen conditioned-Gaussian mass sample, a phase-indexed family of
reduced initial states below one common energy ceiling is evolved by the
already constructed canonical global flow.  The resulting genuine Physlib
trajectories satisfy the exact centered Haar identity: every unmatched term
of the finite A0/A1/A2 character expansion vanishes, while the true nonlinear
post-second-Picard correction remains explicit and obeys the deterministic
energy-window bound.

The chosen reduced witnesses need not be measurable in phase.  Therefore the
centered identity is unconditional, while the uncentered expectation theorem
states the genuinely remaining measurability input explicitly.  This is an
analytic selection boundary, not an RPA or kinetic-equation assumption.
-/

namespace ArchonPhysicsConsumers.Thermalization.CanonicalGaussianActualHaarPostSecondPicard

open MeasureTheory
open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.JointMassEnergyCompactness
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.TruncatedGaussianMassLaw
open ArchonPhysics.GaussianIIDMassPhaseEnsemble

noncomputable section

/-- Frozen positive mass configuration supplied by one conditioned-Gaussian
sample. -/
def fixedGaussianMass
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) :
    Lattice.PositiveMassConfig N :=
  ensemble.restrictPositiveMass sample

theorem fixedGaussianMass_admissible
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N]
    (kappa beta g H : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : Omega) :
    (canonicalIIDUniformEnergyShell N kappa beta g H hbeta).MassAdmissible
      (fixedGaussianMass ensemble sample) := by
  intro i
  have hs := ensemble.mass_mem_support i.val sample
  have hmpos := (fixedGaussianMass ensemble sample).mass_pos i
  exact ⟨hs.1, hs.2,
    (inv_le_inv₀ randomMassUpper_pos hmpos).2 hs.2,
    (inv_le_inv₀ hmpos RandomEnsemble.massLower_pos).2 hs.1⟩

/-- Initial-amplitude alignment stated directly in deterministic modal
coordinates.  A fixed-mass radial/Haar initializer discharges this identity
by `modalCoordinates_reconstruct`; no distributional assumption occurs here. -/
def InitialAmplitudeAligned
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (z0 : UnitAddTorus (Lattice.Site N) → ReducedPhaseSpace m) : Prop :=
  ∀ phase,
    complexModeAmplitude (modeFrequency m observed)
      (modalCoordinates m
        (sqrtMassTransform m
          ((z0 phase).1 : HilbertConfiguration N)) observed)
      (modalCoordinates m
        (inverseSqrtMassTransform m
          ((z0 phase).2 : HilbertConfiguration N)) observed) =
      canonicalFreeComplexInitialAmplitude
        radius (modeFrequency m) phase observed

/-- The actual post-second-Picard norm bound supplied by the common Gaussian
mass support and conserved reduced energy. -/
def canonicalGaussianRemainderBound
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g H : Real) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (T : Real) : Real :=
  afterSecondPicardWindowEnvelope m kappa beta g observed
    (actualModalEnergyL1Envelope N (6 / 5 : Real) kappa beta H) radius T * T

/-- Main canonical consumer.  The global flow is genuinely used: the
phase-indexed trajectories are chosen from its exact reduced matching
theorem, then lifted to Physlib.  The exact Haar identity is centered by the
literal nonlinear correction, and that correction has one common explicit
bound for every phase. -/
theorem exists_canonicalGaussianHaarTrajectory_matchedCharge_decomposition
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    {kappa beta g H T : Real}
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (z0 : UnitAddTorus (Lattice.Site N) →
      ReducedPhaseSpace (fixedGaussianMass ensemble sample))
    (henergy0 : ∀ phase, reducedHamiltonian
      (fixedGaussianMass ensemble sample) kappa beta g (z0 phase) ≤ H)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency
      (fixedGaussianMass ensemble sample) observed)
    (hinitial : InitialAmplitudeAligned
      (fixedGaussianMass ensemble sample) observed radius z0)
    (hT : 0 ≤ T) :
    ∃ z : UnitAddTorus (Lattice.Site N) → Real →
        ReducedPhaseSpace (fixedGaussianMass ensemble sample),
      (∀ phase, z phase 0 = z0 phase) ∧
      (∀ phase time, HasDerivAt (z phase)
        (reducedVectorField (fixedGaussianMass ensemble sample)
          kappa beta g (z phase time)) time) ∧
      (∀ phase time,
        canonicalIIDRandomMassGlobalFlow N kappa beta g H hbeta
            (embedReducedPoint (fixedGaussianMass ensemble sample)
              kappa beta g (z0 phase), time) =
          embedReducedPoint (fixedGaussianMass ensemble sample)
            kappa beta g (z phase time)) ∧
      let p : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N :=
        fun phase ↦ physlibMomentumPathOfReducedTrajectory (z phase)
      let q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N :=
        fun phase ↦ physlibPositionPathOfReducedTrajectory (z phase)
      (∫ phase : UnitAddTorus (Lattice.Site N),
        (actualPhaseModalNormSq
            (fixedGaussianMass ensemble sample) observed p q T phase -
          actualPostSecondPicardEnergyCorrection
            (fixedGaussianMass ensemble sample) kappa beta g observed
              q radius T phase)
        ∂finitePhaseHaarLaw (Lattice.Site N)) =
        physlibMatchedChargeTwoStepMoment
          (fixedGaussianMass ensemble sample) kappa beta g radius T observed ∧
      ∀ phase,
        |actualPostSecondPicardEnergyCorrection
          (fixedGaussianMass ensemble sample) kappa beta g observed
            q radius T phase| ≤
          2 * finiteCharacterTwoStepAbsMass g
              (freeInitialPhaseCoefficient radius
                (modeFrequency (fixedGaussianMass ensemble sample)) observed)
              (physlibQuadraticFirstPicardCharacterCoefficient
                (fixedGaussianMass ensemble sample) kappa radius T observed)
              (completeSecondPicardCoefficient
                (fixedGaussianMass ensemble sample) kappa beta radius observed T) *
              canonicalGaussianRemainderBound
                (fixedGaussianMass ensemble sample) kappa beta g H observed radius T +
            canonicalGaussianRemainderBound
                (fixedGaussianMass ensemble sample) kappa beta g H observed radius T ^ 2 := by
  let m : Lattice.PositiveMassConfig N := fixedGaussianMass ensemble sample
  let shell := canonicalIIDUniformEnergyShell N kappa beta g H hbeta
  have hmass : shell.MassAdmissible m := by
    simpa [shell, m] using
      fixedGaussianMass_admissible ensemble kappa beta g H hbeta sample
  have hexists : ∀ phase : UnitAddTorus (Lattice.Site N),
      ∃ trajectory : Real → ReducedPhaseSpace m,
        trajectory 0 = z0 phase ∧
        (∀ time, HasDerivAt trajectory
          (reducedVectorField m kappa beta g (trajectory time)) time) ∧
        (∀ time, canonicalRandomMassGlobalFlow shell
          (embedReducedPoint m kappa beta g (z0 phase), time) =
            embedReducedPoint m kappa beta g (trajectory time)) ∧
        (∀ time, ‖canonicalRandomMassGlobalFlow shell
          (embedReducedPoint m kappa beta g (z0 phase), time)‖ ≤
            shell.cutoffRadius) ∧
        (∀ time, HasDerivAt
          (fun s ↦ canonicalRandomMassGlobalFlow shell
            (embedReducedPoint m kappa beta g (z0 phase), s))
          (parameterizedHamiltonVectorField
            (canonicalRandomMassGlobalFlow shell
              (embedReducedPoint m kappa beta g (z0 phase), time))) time) ∧
        (∀ time, reducedHamiltonian m kappa beta g (trajectory time) =
          reducedHamiltonian m kappa beta g (z0 phase)) ∧
        ∀ time, reducedJointPoint m (trajectory time) ∈
          jointMassInverseEnergySublevel shell.mLower shell.mUpper
            shell.uLower shell.uUpper kappa beta g H := by
    intro phase
    simpa [shell, canonicalIIDUniformEnergyShell] using
      canonicalRandomMassGlobalFlow_matches_reduced
      shell m hmass (z0 phase) (henergy0 phase)
  choose z hz0 hz hmatch _hflowBound _hflowDeriv henergyConserved _hjoint
    using hexists
  let p : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N :=
    fun phase ↦ physlibMomentumPathOfReducedTrajectory (z phase)
  let q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N :=
    fun phase ↦ physlibPositionPathOfReducedTrajectory (z phase)
  have hp : ∀ phase, Differentiable Real (p phase) := fun phase ↦
    differentiable_physlibMomentumPathOfReducedTrajectory
      m kappa beta g (z phase) (hz phase)
  have hq : ∀ phase, Differentiable Real (q phase) := fun phase ↦
    differentiable_physlibPositionPathOfReducedTrajectory
      m kappa beta g (z phase) (hz phase)
  have hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase) :=
    fun phase ↦ satisfiesHamiltonEquations_physlibPathsOfReducedTrajectory
      m kappa beta g (z phase) (hz phase)
  have hinitialPaths : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed := by
    intro phase
    unfold p q physlibModeAmplitude physlibModePosition physlibModeMomentum
      massWeightedPosition massWeightedMomentum
    rw [realReparametrize_physlibPositionPathOfReducedTrajectory,
      realReparametrize_physlibMomentumPathOfReducedTrajectory,
      hz0 phase]
    exact hinitial phase
  have hcentered :=
    integral_actualPhaseModalNormSq_sub_correction_eq_matchedCharge
      m kappa beta g observed p q hp hq hHamilton radius homega
        hinitialPaths T
  have hmassUpper : ∀ i : Lattice.Site N, m.mass i ≤ (6 / 5 : Real) := by
    intro i
    simpa [m, fixedGaussianMass, RandomEnsemble.massUpper] using
      (ensemble.mass_mem_support i.val sample).2
  have hR : ∀ phase,
      ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        m kappa beta g observed (q phase) radius phase T‖ ≤
        canonicalGaussianRemainderBound
          m kappa beta g H observed radius T := by
    intro phase
    apply norm_afterSecondPicardRemainderCoefficient_le_energyWindow
      m (mUpper := (6 / 5 : Real)) (kappa := kappa) (beta := beta)
        (g := g) (H := H) (T := T) (by norm_num) hmassUpper hbeta
        observed (p phase) (q phase) radius phase homega hT
    · intro time htime
      exact massGauge_realReparametrize_physlibPositionPath m (z phase) time
    · intro time htime
      rw [hamiltonian_realReparametrize_physlibPaths_eq_reducedHamiltonian,
        henergyConserved phase time]
      exact henergy0 phase
  have hcorrectionBound : ∀ phase,
      |actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius T phase| ≤
        2 * finiteCharacterTwoStepAbsMass g
            (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
            (physlibQuadraticFirstPicardCharacterCoefficient
              m kappa radius T observed)
            (completeSecondPicardCoefficient
              m kappa beta radius observed T) *
            canonicalGaussianRemainderBound
              m kappa beta g H observed radius T +
          canonicalGaussianRemainderBound
              m kappa beta g H observed radius T ^ 2 := by
    intro phase
    exact abs_actualPostSecondPicardEnergyCorrection_le
      m kappa beta g observed q radius T phase homega (hR phase)
  refine ⟨z, hz0, hz, ?_, ?_⟩
  · intro phase time
    simpa [canonicalIIDRandomMassGlobalFlow, shell, m] using hmatch phase time
  · dsimp only
    constructor
    · simpa [m, p, q] using hcentered
    · simpa [m, p, q] using hcorrectionBound

#print axioms fixedGaussianMass_admissible
#print axioms integral_unmatchedChargePairCharacterSum_eq_zero
#print axioms integral_actualPhaseModalNormSq_sub_correction_eq_matchedCharge
#print axioms integral_actualPhaseModalNormSq_eq_matchedCharge_add_boundedCorrection
#print axioms abs_actualPostSecondPicardEnergyCorrection_le
#print axioms exists_canonicalGaussianHaarTrajectory_matchedCharge_decomposition

end

end ArchonPhysicsConsumers.Thermalization.CanonicalGaussianActualHaarPostSecondPicard
