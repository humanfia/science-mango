import ArchonPhysics.FixedMassHaarReducedInitialFlowAdapter
import ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation
import ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
import ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

/-!
# Fixed-mass canonical Haar Picard collision decomposition

For one admissible frozen mass realization, this module feeds the explicit
radial/Haar initializer into the canonical measurable microscopic flow.  On a
common energy shell every phase path is an exact Physlib Hamiltonian solution.
The first two Picard layers are finite character families, so Haar averaging
removes every unmatched-charge ordered pair exactly.  All matched-charge
pairs, including repeated-history/recollision pairs, remain in the explicit
finite collision polynomial.  The difference from the true nonlinear orbit
is retained literally and bounded by the proved finite-volume energy-window
remainder envelope.

No fresh-phase restart, RPA hypothesis, Markov closure, or kinetic-time decay
is asserted.
-/

namespace ArchonPhysics.CanonicalFixedMassHaarPicardCollisionDecomposition

open MeasureTheory
open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FixedMassHaarReducedInitialFlowAdapter
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-! ## One combined physical A0/A1/A2 character family -/

/-- Disjoint union of the free, first-Picard, and complete second-Picard
character indices. -/
abbrev CanonicalTwoStepCharacterTerm (N : Nat) :=
  FreeInitialPhaseTerm ⊕
    (QuadraticPhaseTerm N ⊕ CompleteSecondPicardCharacterTerm N)

/-- Coupling-weighted coefficient of the complete physical two-step family. -/
def canonicalTwoStepCharacterCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    CanonicalTwoStepCharacterTerm N → Complex
  | Sum.inl term =>
      freeInitialPhaseCoefficient radius (modeFrequency m) observed term
  | Sum.inr (Sum.inl term) =>
      (g : Complex) *
        physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed term
  | Sum.inr (Sum.inr term) =>
      ((g ^ 2 : Real) : Complex) *
        completeSecondPicardCoefficient
          m kappa beta radius observed time term

/-- Haar charge of the complete physical two-step family. -/
def canonicalTwoStepCharacterCharge
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    CanonicalTwoStepCharacterTerm N → Lattice.Site N → Int
  | Sum.inl term => freeInitialPhaseCharge observed term
  | Sum.inr (Sum.inl term) => quadraticPhaseCharge term
  | Sum.inr (Sum.inr term) => completeSecondPicardCharge term

/-- Every unmatched ordered pair in the combined physical A0/A1/A2 family
has exactly zero fixed-mass Haar expectation.  This includes cross-family and
within-family pairs; only equal-charge collision/recollision pairs survive. -/
theorem integral_canonicalTwoStepUnmatchedPairSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      unmatchedChargePairCharacterSum
        (canonicalTwoStepCharacterCoefficient
          m kappa beta g radius time observed)
        (canonicalTwoStepCharacterCharge observed)
        (canonicalTwoStepCharacterCoefficient
          m kappa beta g radius time observed)
        (canonicalTwoStepCharacterCharge observed) phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) = 0 := by
  exact integral_unmatchedChargePairCharacterSum_eq_zero
    (canonicalTwoStepCharacterCoefficient
      m kappa beta g radius time observed)
    (canonicalTwoStepCharacterCharge observed)
    (canonicalTwoStepCharacterCoefficient
      m kappa beta g radius time observed)
    (canonicalTwoStepCharacterCharge observed)

/-! ## Explicit true-orbit remainder envelope -/

/-- Microscopic post-second-Picard norm envelope for a fixed admissible mass
sample in a common canonical energy shell. -/
def canonicalFixedMassHaarRemainderBound
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (T : Real) : Real :=
  afterSecondPicardWindowEnvelope m shell.kappa shell.beta shell.g observed
    (actualModalEnergyL1Envelope N shell.mUpper shell.kappa shell.beta shell.H)
    radius T * T

/-- Uniform deterministic bound on the literal nonlinear energy correction. -/
def canonicalFixedMassHaarEnergyCorrectionBound
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (T : Real) : Real :=
  2 * finiteCharacterTwoStepAbsMass shell.g
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (physlibQuadraticFirstPicardCharacterCoefficient
        m shell.kappa radius T observed)
      (completeSecondPicardCoefficient
        m shell.kappa shell.beta radius observed T) *
      canonicalFixedMassHaarRemainderBound shell m observed radius T +
    canonicalFixedMassHaarRemainderBound shell m observed radius T ^ 2

/-! ## Canonical fixed-mass actual decomposition -/

/-- The fixed-mass Haar initializer on the canonical ambient flow gives
genuine Physlib solutions at every phase.  Its actual modal Haar expectation
is exactly the complete matched-charge A0/A1/A2 polynomial plus the literal
nonlinear correction, whose expectation obeys the displayed microscopic
bound. -/
theorem canonicalFixedMassHaar_actualPicard_decomposition
    {N : Nat} [NeZero N] (shell : UniformRandomMassEnergyShell N)
    (m : Lattice.PositiveMassConfig N) (hmass : shell.MassAdmissible m)
    (radius : Lattice.Site N → Real)
    (hzero : ∀ k, modeFrequency m k = 0 → radius k = 0)
    (henergy0 : ∀ phase : UnitAddTorus (Lattice.Site N),
      reducedHamiltonian m shell.kappa shell.beta shell.g
        (fixedMassHaarReducedInitialState m radius hzero phase) ≤ shell.H)
    (observed : Lattice.Site N) (homega : 0 < modeFrequency m observed)
    (T : Real) (hT : 0 ≤ T) :
    let p : UnitAddTorus (Lattice.Site N) →
        Time → HilbertConfiguration N :=
      fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero
    let q : UnitAddTorus (Lattice.Site N) →
        Time → HilbertConfiguration N :=
      fixedMassHaarCanonicalPhyslibPosition shell m radius hzero
    (∀ phase, Differentiable Real (p phase)) ∧
      (∀ phase, Differentiable Real (q phase)) ∧
      (∀ phase, SatisfiesHamiltonEquations
        m shell.kappa shell.beta shell.g (p phase) (q phase)) ∧
      Measurable (actualPostSecondPicardEnergyCorrection
        m shell.kappa shell.beta shell.g observed q radius T) ∧
      ((∫ phase : UnitAddTorus (Lattice.Site N),
          actualPhaseModalNormSq m observed p q T phase
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
        physlibMatchedChargeTwoStepMoment
            m shell.kappa shell.beta shell.g radius T observed +
          ∫ phase : UnitAddTorus (Lattice.Site N),
            actualPostSecondPicardEnergyCorrection
              m shell.kappa shell.beta shell.g observed q radius T phase
            ∂finitePhaseHaarLaw (Lattice.Site N)) ∧
      |∫ phase : UnitAddTorus (Lattice.Site N),
        actualPostSecondPicardEnergyCorrection
          m shell.kappa shell.beta shell.g observed q radius T phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤
          canonicalFixedMassHaarEnergyCorrectionBound
            shell m observed radius T := by
  let p : UnitAddTorus (Lattice.Site N) →
      Time → HilbertConfiguration N :=
    fixedMassHaarCanonicalPhyslibMomentum shell m radius hzero
  let q : UnitAddTorus (Lattice.Site N) →
      Time → HilbertConfiguration N :=
    fixedMassHaarCanonicalPhyslibPosition shell m radius hzero
  have hwitness : ∀ phase : UnitAddTorus (Lattice.Site N),
      ∃ z : Real → ReducedPhaseSpace m,
        z 0 = fixedMassHaarReducedInitialState m radius hzero phase ∧
        (∀ time, HasDerivAt z
          (reducedVectorField m shell.kappa shell.beta shell.g (z time)) time) ∧
        (∀ time, canonicalRandomMassGlobalFlow shell
          (fixedMassHaarParametricInitial shell m radius hzero phase, time) =
            embedReducedPoint m shell.kappa shell.beta shell.g (z time)) ∧
        p phase = physlibMomentumPathOfReducedTrajectory z ∧
        q phase = physlibPositionPathOfReducedTrajectory z ∧
        Differentiable Real (p phase) ∧
        Differentiable Real (q phase) ∧
        SatisfiesHamiltonEquations m shell.kappa shell.beta shell.g
          (p phase) (q phase) ∧
        ∀ time, reducedHamiltonian m shell.kappa shell.beta shell.g (z time) =
          reducedHamiltonian m shell.kappa shell.beta shell.g
            (fixedMassHaarReducedInitialState m radius hzero phase) := by
    intro phase
    simpa [p, q] using
      exists_reducedTrajectory_matching_fixedMassHaarCanonicalPhyslibPaths
        shell m hmass radius hzero phase (henergy0 phase)
  choose z hz0 hz hmatch hpPath hqPath hp hq hHamilton henergyConserved
    using hwitness
  have hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed := by
    intro phase
    have htimeZero : Time.toRealCLE.symm (0 : Real) = (0 : Time) := by
      exact map_zero Time.toRealCLE.symm
    unfold physlibModeAmplitude physlibModePosition physlibModeMomentum
      massWeightedPosition massWeightedMomentum realReparametrize
    rw [htimeZero]
    change
      ArchonPhysics.ComplexModeAmplitude.complexModeAmplitude
        (modeFrequency m observed)
        (modalCoordinates m
          (sqrtMassTransform m (q phase 0)) observed)
        (modalCoordinates m
          (inverseSqrtMassTransform m (p phase 0)) observed) = _
    rw [show q phase 0 = fixedMassHaarPhysicalPosition m radius phase by
        simp [q],
      show p phase 0 = fixedMassHaarPhysicalMomentum m radius phase by
        simp [p]]
    exact complexModeAmplitude_fixedMassHaarInitial_eq_canonicalFree
      m radius phase observed
  have hactualMeasurable : Measurable
      (actualPhaseModalNormSq m observed p q T) := by
    have hamp : Measurable (fun phase : UnitAddTorus (Lattice.Site N) ↦
        physlibModeAmplitude m observed (p phase) (q phase) T) := by
      simpa [p, q] using
        measurable_fixedMassHaarPhyslibModeAmplitude_at
          shell m radius hzero observed T
    have hcontinuous : Continuous (fun A : Complex ↦
        Complex.normSq
          (phaseRenormalize (modeFrequency m observed * T) A)) := by
      unfold phaseRenormalize
      fun_prop
    exact hcontinuous.measurable.comp hamp
  have htwoStepMeasurable : Measurable
      (fun phase : UnitAddTorus (Lattice.Site N) ↦
        Complex.normSq
          (twoStepPerturbedAmplitude shell.g
            (canonicalFreeComplexInitialAmplitude
              radius (modeFrequency m) phase observed)
            (physlibQuadraticFirstPicardCoefficient
              m shell.kappa radius phase T observed)
            (physlibFPUTSecondPicardCoefficient
              m shell.kappa shell.beta observed radius phase T))) := by
    let zCoefficient :=
      freeInitialPhaseCoefficient radius (modeFrequency m) observed
    let wCoefficient :=
      physlibQuadraticFirstPicardCharacterCoefficient
        m shell.kappa radius T observed
    let uCoefficient :=
      completeSecondPicardCoefficient
        m shell.kappa shell.beta radius observed T
    have hcontinuous : Continuous
        (fun phase : UnitAddTorus (Lattice.Site N) ↦
          Complex.normSq
            (finiteCharacterFamilyTwoStepAmplitude shell.g
              zCoefficient (freeInitialPhaseCharge observed)
              wCoefficient quadraticPhaseCharge
              uCoefficient completeSecondPicardCharge phase)) := by
      unfold finiteCharacterFamilyTwoStepAmplitude twoStepPerturbedAmplitude
      have hz := finitePhaseCorrection_continuous
        zCoefficient (freeInitialPhaseCharge observed)
      have hw := finitePhaseCorrection_continuous
        wCoefficient quadraticPhaseCharge
      have hu := finitePhaseCorrection_continuous
        uCoefficient completeSecondPicardCharge
      fun_prop
    have heq :
        (fun phase : UnitAddTorus (Lattice.Site N) ↦
          Complex.normSq
            (twoStepPerturbedAmplitude shell.g
              (canonicalFreeComplexInitialAmplitude
                radius (modeFrequency m) phase observed)
              (physlibQuadraticFirstPicardCoefficient
                m shell.kappa radius phase T observed)
              (physlibFPUTSecondPicardCoefficient
                m shell.kappa shell.beta observed radius phase T))) =
          fun phase ↦ Complex.normSq
            (finiteCharacterFamilyTwoStepAmplitude shell.g
              zCoefficient (freeInitialPhaseCharge observed)
              wCoefficient quadraticPhaseCharge
              uCoefficient completeSecondPicardCharge phase) := by
      funext phase
      dsimp only [zCoefficient, wCoefficient, uCoefficient]
      rw [physlibTwoStepAmplitude_eq_finiteCharacterFamily
        m shell.kappa shell.beta shell.g radius phase T observed homega]
    rw [heq]
    exact hcontinuous.measurable
  have hpointwise := actualPhaseModalNormSq_eq_twoStep_add_correction
    m shell.kappa shell.beta shell.g observed p q hp hq hHamilton radius
      homega hinitial T
  have hcorrectionEq :
      actualPostSecondPicardEnergyCorrection
          m shell.kappa shell.beta shell.g observed q radius T =
        fun phase ↦ actualPhaseModalNormSq m observed p q T phase -
          Complex.normSq
            (twoStepPerturbedAmplitude shell.g
              (canonicalFreeComplexInitialAmplitude
                radius (modeFrequency m) phase observed)
              (physlibQuadraticFirstPicardCoefficient
                m shell.kappa radius phase T observed)
              (physlibFPUTSecondPicardCoefficient
                m shell.kappa shell.beta observed radius phase T)) := by
    funext phase
    have h := hpointwise phase
    linarith
  have hcorrectionMeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m shell.kappa shell.beta shell.g observed q radius T) := by
    rw [hcorrectionEq]
    exact hactualMeasurable.sub htwoStepMeasurable
  have hmUpper0 : 0 ≤ shell.mUpper := by
    exact (m.mass_pos 0).le.trans (hmass 0).2.1
  have hmassUpper : ∀ i, m.mass i ≤ shell.mUpper := fun i ↦
    (hmass i).2.1
  have hR : ∀ phase,
      ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        m shell.kappa shell.beta shell.g observed (q phase) radius phase T‖ ≤
        canonicalFixedMassHaarRemainderBound
          shell m observed radius T := by
    intro phase
    unfold canonicalFixedMassHaarRemainderBound
    apply norm_afterSecondPicardRemainderCoefficient_le_energyWindow
      m hmUpper0 hmassUpper shell.hbeta observed (p phase) (q phase)
        radius phase homega hT
    · intro time htime
      rw [hqPath phase]
      exact massGauge_realReparametrize_physlibPositionPath m (z phase) time
    · intro time htime
      rw [hpPath phase, hqPath phase,
        hamiltonian_realReparametrize_physlibPaths_eq_reducedHamiltonian,
        henergyConserved phase time]
      exact henergy0 phase
  have hcorrectionBound : ∀ phase,
      |actualPostSecondPicardEnergyCorrection
        m shell.kappa shell.beta shell.g observed q radius T phase| ≤
        canonicalFixedMassHaarEnergyCorrectionBound
          shell m observed radius T := by
    intro phase
    unfold canonicalFixedMassHaarEnergyCorrectionBound
    exact abs_actualPostSecondPicardEnergyCorrection_le
      m shell.kappa shell.beta shell.g observed q radius T phase homega
        (hR phase)
  have hexpectation :=
    integral_actualPhaseModalNormSq_eq_matchedCharge_add_boundedCorrection
      m shell.kappa shell.beta shell.g observed p q hp hq hHamilton radius
        homega hinitial T hcorrectionMeasurable hcorrectionBound
  exact ⟨hp, hq, hHamilton, hcorrectionMeasurable,
    hexpectation.1, hexpectation.2⟩

end

end ArchonPhysics.CanonicalFixedMassHaarPicardCollisionDecomposition
