import ArchonPhysics.OrderedPositiveInitialEnergyProfile
import ArchonPhysics.PhaseEnergyModeCoordinates
import ArchonPhysics.RandomMassMeasurableOrderedEigenframe
import ArchonPhysics.SignedEigenframeModeAssembly

/-!
# Measurable random-mass initial data from a frozen energy profile and Haar phases

This module performs the previously missing dependent initial-data assembly.
The deterministic profile on the first `N - 1` ordered modes is converted to
real modal coordinates using the iid Haar phases, then reconstructed in the
explicit globally measurable signed eigenframe.  Finally the mass-weighted
variables are converted to physical position and canonical momentum.

All maps are globally totalized and measurable, including on the null set of
degenerate spectra.  On the almost-sure simple-spectrum event, every ordered
physical harmonic energy is exactly the prescribed profile; the final
translation mode has zero energy.  No kinetic-limit statement is made here.
-/

namespace ArchonPhysics.RandomMassPhaseInitialData

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.SignedEigenframeModeAssembly
open scoped BigOperators Matrix

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The definitional cardinality equivalence between ordered mode indices and
the `N` site indices. -/
def orderedModeIndexEquivFin
    (N : Nat) [NeZero N] : OrderedModeIndex N ≃ Fin N :=
  finCongr (by simp)

/-- Frozen target energy on all ordered indices, with zero assigned to the
fixed last translation index. -/
def orderedTargetEnergy
    (N : Nat) [NeZero N] (a : Real) (k : OrderedModeIndex N) : Real :=
  orderedPositiveInitialEnergyProfile N a (orderedModeIndexEquivFin N k)

/-- The last ordered target energy is zero. -/
@[simp] theorem orderedTargetEnergy_last
    {N : Nat} [NeZero N] (a : Real) :
    orderedTargetEnergy N a
      (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
  have hlast : orderedModeIndexEquivFin N
      (lastOrderedIndex (ι := Lattice.Site N)) = lastSiteOrderedIndex N := by
    apply Fin.ext
    simp [orderedModeIndexEquivFin, lastOrderedIndex, lastSiteOrderedIndex]
  rw [orderedTargetEnergy, hlast,
    orderedPositiveInitialEnergyProfile_last]

/-- The ordered target profile retains total energy one. -/
theorem sum_orderedTargetEnergy_eq_one
    {N : Nat} [NeZero N] (hN : 3 ≤ N) (a : Real) :
    (∑ k : OrderedModeIndex N, orderedTargetEnergy N a k) = 1 := by
  calc
    (∑ k : OrderedModeIndex N, orderedTargetEnergy N a k) =
        ∑ i : Fin N, orderedPositiveInitialEnergyProfile N a i := by
      exact Fintype.sum_equiv (orderedModeIndexEquivFin N)
        (orderedTargetEnergy N a)
        (orderedPositiveInitialEnergyProfile N a) (fun _ => rfl)
    _ = 1 := sum_orderedPositiveInitialEnergyProfile_eq_one hN a

/-- Haar phase attached to one ordered mode.  The last phase is harmlessly
unused because its target energy is zero. -/
def orderedPhaseSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (k : OrderedModeIndex N) :
    UnitAddCircle :=
  ensemble.phase (orderedModeIndexEquivFin N k).val omega

/-- Ordered frequency of the random mass-weighted harmonic matrix. -/
def orderedFrequencySample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (k : OrderedModeIndex N) : Real :=
  orderedModeFrequency
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)) omega) k

/-- Random real position coefficient in the explicit signed eigenframe. -/
def initialModePositionCoefficient
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real)
    (omega : Omega) (k : OrderedModeIndex N) : Real :=
  phaseCoordinate (orderedTargetEnergy N a k)
    (orderedFrequencySample ensemble omega k)
    (orderedPhaseSample ensemble omega k)

/-- Random real momentum coefficient in the explicit signed eigenframe. -/
def initialModeMomentumCoefficient
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real)
    (omega : Omega) (k : OrderedModeIndex N) : Real :=
  phaseMomentum (orderedTargetEnergy N a k)
    (orderedPhaseSample ensemble omega k)

/-- All scalar position--momentum coefficients are globally measurable. -/
theorem measurable_initialModeCoefficients
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) :
    Measurable fun omega => fun k : OrderedModeIndex N =>
      (initialModePositionCoefficient ensemble a omega k,
        initialModeMomentumCoefficient ensemble a omega k) := by
  apply measurable_pi_lambda
  intro k
  have hsample : Measurable
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := N))) :=
    measurable_harmonicHermitianSample _
      (RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
        ensemble)
  have hfrequency : Measurable fun omega =>
      orderedFrequencySample ensemble omega k := by
    exact (((OrderedSpectrumContinuity.continuous_orderedEigenvalue k).measurable.comp
      hsample).sqrt)
  have hphase : Measurable fun omega => orderedPhaseSample ensemble omega k := by
    exact ensemble.phase_measurable (orderedModeIndexEquivFin N k).val
  have hinput : Measurable fun omega =>
      (orderedTargetEnergy N a k,
        (orderedFrequencySample ensemble omega k,
          orderedPhaseSample ensemble omega k)) :=
    measurable_const.prodMk (hfrequency.prodMk hphase)
  exact measurable_phaseModeCoordinates.comp hinput

theorem measurable_initialModePositionCoefficient
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) :
    Measurable (initialModePositionCoefficient ensemble (N := N) a) :=
  by
    apply measurable_pi_lambda
    intro k
    exact ((measurable_initialModeCoefficients ensemble a).eval).fst

theorem measurable_initialModeMomentumCoefficient
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) :
    Measurable (initialModeMomentumCoefficient ensemble (N := N) a) :=
  by
    apply measurable_pi_lambda
    intro k
    exact ((measurable_initialModeCoefficients ensemble a).eval).snd

/-- Reconstructed mass-weighted initial position `X = sqrt(M) q`. -/
def initialMassWeightedPosition
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega) :
    Lattice.Configuration N :=
  signedFrameReconstruction
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)) omega)
    (initialModePositionCoefficient ensemble a omega)

/-- Reconstructed mass-weighted initial momentum `Y = M^(-1/2) p`. -/
def initialMassWeightedMomentum
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega) :
    Lattice.Configuration N :=
  signedFrameReconstruction
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)) omega)
    (initialModeMomentumCoefficient ensemble a omega)

theorem measurable_initialMassWeightedPosition
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) :
    Measurable (initialMassWeightedPosition ensemble (N := N) a) := by
  exact measurable_signedFrameReconstruction
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)))
    (measurable_harmonicHermitianSample _
      (RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
        ensemble)) _
    (measurable_initialModePositionCoefficient ensemble a)

theorem measurable_initialMassWeightedMomentum
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) :
    Measurable (initialMassWeightedMomentum ensemble (N := N) a) := by
  exact measurable_signedFrameReconstruction
    (harmonicHermitianSample
      (ensemble.restrictPositiveMass (N := N)))
    (measurable_harmonicHermitianSample _
      (RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
        ensemble)) _
    (measurable_initialModeMomentumCoefficient ensemble a)

/-- Physical position obtained from `X` by inverse square-root mass scaling. -/
def initialPhysicalPosition
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega) :
    CoerciveHamiltonianPhyslib.HilbertConfiguration N :=
  WithLp.toLp 2 fun i =>
    (Real.sqrt
      ((ensemble.restrictPositiveMass (N := N) omega).mass i))⁻¹ *
      initialMassWeightedPosition ensemble a omega i

/-- Physical canonical momentum obtained from `Y` by square-root mass scaling. -/
def initialPhysicalMomentum
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega) :
    CoerciveHamiltonianPhyslib.HilbertConfiguration N :=
  WithLp.toLp 2 fun i =>
    Real.sqrt ((ensemble.restrictPositiveMass (N := N) omega).mass i) *
      initialMassWeightedMomentum ensemble a omega i

theorem measurable_initialPhysicalPosition
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) :
    Measurable (initialPhysicalPosition ensemble (N := N) a) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  exact ((RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
    ensemble i).sqrt.inv).mul
      ((measurable_initialMassWeightedPosition ensemble a).eval)

theorem measurable_initialPhysicalMomentum
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) :
    Measurable (initialPhysicalMomentum ensemble (N := N) a) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  exact ((RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
    ensemble i).sqrt).mul
      ((measurable_initialMassWeightedMomentum ensemble a).eval)

/-- The physical position transforms back to the reconstructed `X` exactly. -/
theorem sqrtMassTransform_initialPhysicalPosition
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega) :
    sqrtMassTransform (ensemble.restrictPositiveMass (N := N) omega)
        (initialPhysicalPosition ensemble a omega) =
      WithLp.toLp 2 (initialMassWeightedPosition ensemble a omega) := by
  ext i
  rw [sqrtMassTransform_apply]
  unfold initialPhysicalPosition
  rw [← mul_assoc, mul_inv_cancel₀
    (Real.sqrt_ne_zero'.2
      ((ensemble.restrictPositiveMass (N := N) omega).mass_pos i)), one_mul]

/-- The physical momentum transforms back to the reconstructed `Y` exactly. -/
theorem inverseSqrtMassTransform_initialPhysicalMomentum
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (a : Real) (omega : Omega) :
    inverseSqrtMassTransform (ensemble.restrictPositiveMass (N := N) omega)
        (initialPhysicalMomentum ensemble a omega) =
      WithLp.toLp 2 (initialMassWeightedMomentum ensemble a omega) := by
  ext i
  rw [inverseSqrtMassTransform_apply]
  unfold initialPhysicalMomentum
  rw [← mul_assoc, inv_mul_cancel₀
    (Real.sqrt_ne_zero'.2
      ((ensemble.restrictPositiveMass (N := N) omega).mass_pos i)), one_mul]

/-- On a simple realization, every basis-free physical ordered energy equals
the prescribed deterministic target energy. -/
theorem orderedHarmonicModeEnergy_initial_eq_target
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := N)) omega))
    (k : OrderedModeIndex N) :
    MeasurableOrderedHarmonicEnergy.orderedHarmonicModeEnergy
        (harmonicHermitianSample
          (ensemble.restrictPositiveMass (N := N)) omega) k
        (initialMassWeightedPosition ensemble a omega)
        (initialMassWeightedMomentum ensemble a omega) =
      orderedTargetEnergy N a k := by
  let A := harmonicHermitianSample
    (ensemble.restrictPositiveMass (N := N)) omega
  rw [show initialMassWeightedPosition ensemble a omega =
      signedFrameReconstruction A
        (initialModePositionCoefficient ensemble a omega) by rfl,
    show initialMassWeightedMomentum ensemble a omega =
      signedFrameReconstruction A
        (initialModeMomentumCoefficient ensemble a omega) by rfl,
    orderedHarmonicModeEnergy_reconstruction A hsimple]
  have heigen_nonneg : 0 ≤ orderedEigenvalue A k := by
    simpa [A, harmonicOrderedEigenvalue] using
      (harmonicOrderedEigenvalue_nonneg
        (ensemble.restrictPositiveMass (N := N)) omega k)
  by_cases hlast : k = lastOrderedIndex (ι := Lattice.Site N)
  · subst k
    have hzero : orderedEigenvalue A
        (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
      simpa [A, harmonicHermitianSample, harmonicHermitian] using
        harmonic_lastOrderedEigenvalue_eq_zero
          (ensemble.restrictPositiveMass (N := N) omega)
    simp [initialModePositionCoefficient, initialModeMomentumCoefficient,
      orderedFrequencySample, hzero, orderedTargetEnergy_last,
      HarmonicModes.modalEnergy, phaseCoordinate, phaseMomentum]
  · have hfrequency : 0 < orderedFrequencySample ensemble omega k := by
      have hpos := (orderedModeFrequency_pos_iff_ne_last
        (ensemble.restrictPositiveMass (N := N) omega) hsimple k).2 hlast
      simpa [orderedFrequencySample, A, harmonicHermitianSample,
        harmonicHermitian] using hpos
    have htarget : 0 ≤ orderedTargetEnergy N a k := by
      exact orderedPositiveInitialEnergyProfile_nonneg hN ha0 ha1 _
    have hsquare : (orderedFrequencySample ensemble omega k) ^ 2 =
        orderedEigenvalue A k := by
      exact Real.sq_sqrt heigen_nonneg
    rw [← hsquare]
    exact modalEnergy_phaseCoordinates _ htarget hfrequency

/-- Almost surely the complete random physical harmonic energy vector is the
frozen target profile. -/
theorem orderedHarmonicModeEnergy_initial_eq_target_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) :
    ∀ᵐ omega ∂ensemble.probability,
      ∀ k : OrderedModeIndex N,
        MeasurableOrderedHarmonicEnergy.orderedHarmonicModeEnergy
            (harmonicHermitianSample
              (ensemble.restrictPositiveMass (N := N)) omega) k
            (initialMassWeightedPosition ensemble a omega)
            (initialMassWeightedMomentum ensemble a omega) =
          orderedTargetEnergy N a k := by
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
    (N := N) ensemble (by omega)] with omega hsimple
  intro k
  exact orderedHarmonicModeEnergy_initial_eq_target
    ensemble hN ha0 ha1 omega hsimple k

end

end ArchonPhysics.RandomMassPhaseInitialData
