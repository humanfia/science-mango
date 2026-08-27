import ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
import ArchonPhysics.GaussianRandomMassSimpleSpectrum
import ArchonPhysics.PhysicalHarmonicEnergyIdentity
import ArchonPhysics.RandomMassPhaseInitialData
import ArchonPhysics.SignedEigenframeModeAssembly

/-!
# Physical initial data for the concrete Gaussian two-band ensemble

This module closes the finite-volume physical-coordinate adapter left open by
`ConcreteGaussianTwoBandInitialEnsemble`.  For every sample it constructs
modal coordinates with the prescribed extensive two-band energies, assembles
them in the globally measurable signed ordered eigenframe, and converts the
mass-weighted variables

`X = sqrt(M) q`, `Y = M^(-1/2) p`

back to physical position and canonical momentum.  The maps are measurable
on the whole sample space, including the null set of degenerate spectra.

For nonnegative energy density and `N >= 3`, Gaussian simple spectrum implies
almost surely that every physical ordered harmonic mode has exactly its
prescribed energy and that the total physical harmonic Hamiltonian is
`N * energyDensity`.

No nonlinear propagation, kinetic limit, or thermalization assertion is made.
-/

namespace ArchonPhysics.ConcreteGaussianTwoBandPhysicalInitialData

open ArchonPhysics
open ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhysicalHarmonicEnergyIdentity
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.SignedEigenframeModeAssembly
open MeasureTheory
open scoped BigOperators Matrix

noncomputable section

/-- The positive finite mass realization used by the concrete ensemble. -/
def massSample {N : Nat} [NeZero N] (sample : SampleSpace) :
    Lattice.PositiveMassConfig N :=
  concreteEnsemble.restrictPositiveMass sample

/-- Every physical mass coordinate is globally measurable. -/
theorem measurable_massSample_coordinate
    {N : Nat} [NeZero N] (site : Lattice.Site N) :
    Measurable fun sample : SampleSpace => (massSample (N := N) sample).mass site := by
  simpa [massSample] using concreteEnsemble.mass_measurable site.val

/-- The concrete Haar phase attached to one ordered mode. -/
def orderedPhase {N : Nat} [NeZero N]
    (sample : SampleSpace) (mode : OrderedMode N) : UnitAddCircle :=
  concreteEnsemble.phase (orderedModeIndexEquivFin N mode).val sample

/-- The actual ordered angular frequency of a concrete Gaussian mass sample. -/
def orderedFrequency {N : Nat} [NeZero N]
    (sample : SampleSpace) (mode : OrderedMode N) : Real :=
  orderedModeFrequency (harmonicHermitian (massSample (N := N) sample)) mode

/-- Initial ordered modal position coefficient carrying the prescribed
two-band energy. -/
def initialModalPosition {N : Nat} [NeZero N] (energyDensity : Real)
    (sample : SampleSpace) (mode : OrderedMode N) : Real :=
  phaseCoordinate (orderedModalEnergy N energyDensity mode)
    (orderedFrequency sample mode) (orderedPhase sample mode)

/-- Initial ordered modal momentum coefficient carrying the prescribed
two-band energy. -/
def initialModalMomentum {N : Nat} [NeZero N] (energyDensity : Real)
    (sample : SampleSpace) (mode : OrderedMode N) : Real :=
  phaseMomentum (orderedModalEnergy N energyDensity mode)
    (orderedPhase sample mode)

/-- The pair of complete modal coefficient vectors is globally measurable. -/
theorem measurable_initialModalCoefficients
    {N : Nat} [NeZero N] (energyDensity : Real) :
    Measurable fun sample : SampleSpace => fun mode : OrderedMode N =>
      (initialModalPosition energyDensity sample mode,
        initialModalMomentum energyDensity sample mode) := by
  apply measurable_pi_lambda
  intro mode
  have hmatrix : Measurable fun sample : SampleSpace =>
      harmonicHermitian (massSample (N := N) sample) :=
    measurable_harmonicHermitianSample massSample
      measurable_massSample_coordinate
  have hfrequency : Measurable fun sample : SampleSpace =>
      orderedFrequency sample mode := by
    exact (((OrderedSpectrumContinuity.continuous_orderedEigenvalue mode).measurable.comp
      hmatrix).sqrt)
  have hphase : Measurable fun sample : SampleSpace =>
      orderedPhase sample mode := by
    exact concreteEnsemble.phase_measurable
      (orderedModeIndexEquivFin N mode).val
  have hinput : Measurable fun sample : SampleSpace =>
      (orderedModalEnergy N energyDensity mode,
        (orderedFrequency sample mode, orderedPhase sample mode)) :=
    measurable_const.prodMk (hfrequency.prodMk hphase)
  exact measurable_phaseModeCoordinates.comp hinput

theorem measurable_initialModalPosition
    {N : Nat} [NeZero N] (energyDensity : Real) :
    Measurable (initialModalPosition (N := N) energyDensity) := by
  apply measurable_pi_lambda
  intro mode
  exact ((measurable_initialModalCoefficients
    (N := N) energyDensity).eval).fst

theorem measurable_initialModalMomentum
    {N : Nat} [NeZero N] (energyDensity : Real) :
    Measurable (initialModalMomentum (N := N) energyDensity) := by
  apply measurable_pi_lambda
  intro mode
  exact ((measurable_initialModalCoefficients
    (N := N) energyDensity).eval).snd

/-- Reconstructed mass-weighted position `X`. -/
def initialMassWeightedPosition {N : Nat} [NeZero N]
    (energyDensity : Real) (sample : SampleSpace) : Lattice.Configuration N :=
  signedFrameReconstruction
    (harmonicHermitian (massSample (N := N) sample))
    (initialModalPosition energyDensity sample)

/-- Reconstructed mass-weighted momentum `Y`. -/
def initialMassWeightedMomentum {N : Nat} [NeZero N]
    (energyDensity : Real) (sample : SampleSpace) : Lattice.Configuration N :=
  signedFrameReconstruction
    (harmonicHermitian (massSample (N := N) sample))
    (initialModalMomentum energyDensity sample)

theorem measurable_initialMassWeightedPosition
    {N : Nat} [NeZero N] (energyDensity : Real) :
    Measurable (initialMassWeightedPosition (N := N) energyDensity) := by
  exact measurable_signedFrameReconstruction
    (fun sample : SampleSpace => harmonicHermitian (massSample (N := N) sample))
    (measurable_harmonicHermitianSample massSample
      measurable_massSample_coordinate) _
    (measurable_initialModalPosition energyDensity)

theorem measurable_initialMassWeightedMomentum
    {N : Nat} [NeZero N] (energyDensity : Real) :
    Measurable (initialMassWeightedMomentum (N := N) energyDensity) := by
  exact measurable_signedFrameReconstruction
    (fun sample : SampleSpace => harmonicHermitian (massSample (N := N) sample))
    (measurable_harmonicHermitianSample massSample
      measurable_massSample_coordinate) _
    (measurable_initialModalMomentum energyDensity)

/-- Physical initial position, obtained from `X` by inverse square-root mass
scaling. -/
def initialPhysicalPosition {N : Nat} [NeZero N]
    (energyDensity : Real) (sample : SampleSpace) :
    CoerciveHamiltonianPhyslib.HilbertConfiguration N :=
  WithLp.toLp 2 fun site =>
    (Real.sqrt ((massSample (N := N) sample).mass site))⁻¹ *
      initialMassWeightedPosition energyDensity sample site

/-- Physical canonical initial momentum, obtained from `Y` by square-root
mass scaling. -/
def initialPhysicalMomentum {N : Nat} [NeZero N]
    (energyDensity : Real) (sample : SampleSpace) :
    CoerciveHamiltonianPhyslib.HilbertConfiguration N :=
  WithLp.toLp 2 fun site =>
    Real.sqrt ((massSample (N := N) sample).mass site) *
      initialMassWeightedMomentum energyDensity sample site

theorem measurable_initialPhysicalPosition
    {N : Nat} [NeZero N] (energyDensity : Real) :
    Measurable (initialPhysicalPosition (N := N) energyDensity) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro site
  exact (measurable_massSample_coordinate site).sqrt.inv.mul
    ((measurable_initialMassWeightedPosition energyDensity).eval)

theorem measurable_initialPhysicalMomentum
    {N : Nat} [NeZero N] (energyDensity : Real) :
    Measurable (initialPhysicalMomentum (N := N) energyDensity) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro site
  exact (measurable_massSample_coordinate site).sqrt.mul
    ((measurable_initialMassWeightedMomentum energyDensity).eval)

/-- The physical position transforms back to the reconstructed `X`. -/
theorem sqrtMassTransform_initialPhysicalPosition
    {N : Nat} [NeZero N] (energyDensity : Real) (sample : SampleSpace) :
    sqrtMassTransform (massSample (N := N) sample)
        (initialPhysicalPosition energyDensity sample) =
      WithLp.toLp 2 (initialMassWeightedPosition energyDensity sample) := by
  ext site
  rw [sqrtMassTransform_apply]
  unfold initialPhysicalPosition
  rw [← mul_assoc, mul_inv_cancel₀
    (Real.sqrt_ne_zero'.2 ((massSample (N := N) sample).mass_pos site)), one_mul]

/-- The physical canonical momentum transforms back to the reconstructed
`Y`. -/
theorem inverseSqrtMassTransform_initialPhysicalMomentum
    {N : Nat} [NeZero N] (energyDensity : Real) (sample : SampleSpace) :
    inverseSqrtMassTransform (massSample (N := N) sample)
        (initialPhysicalMomentum energyDensity sample) =
      WithLp.toLp 2 (initialMassWeightedMomentum energyDensity sample) := by
  ext site
  rw [inverseSqrtMassTransform_apply]
  unfold initialPhysicalMomentum
  rw [← mul_assoc, inv_mul_cancel₀
    (Real.sqrt_ne_zero'.2 ((massSample (N := N) sample).mass_pos site)), one_mul]

/-- The two concrete presentations of the final ordered index agree. -/
theorem lastOrderedIndex_eq_lastSiteOrderedIndex {N : Nat} [NeZero N] :
    lastOrderedIndex (ι := Lattice.Site N) =
      lastSiteOrderedIndex (Fintype.card (Lattice.Site N)) := by
  apply Fin.ext
  simp [lastOrderedIndex, lastSiteOrderedIndex]

/-- On a simple realization, every reconstructed mass-weighted mode has its
prescribed extensive two-band energy. -/
theorem orderedHarmonicModeEnergy_initial_eq_prescribed
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (sample : SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (massSample (N := N) sample)))
    (mode : OrderedMode N) :
    MeasurableOrderedHarmonicEnergy.orderedHarmonicModeEnergy
        (harmonicHermitian (massSample (N := N) sample)) mode
        (initialMassWeightedPosition energyDensity sample)
        (initialMassWeightedMomentum energyDensity sample) =
      orderedModalEnergy N energyDensity mode := by
  let A := harmonicHermitian (massSample (N := N) sample)
  rw [show initialMassWeightedPosition energyDensity sample =
      signedFrameReconstruction A
        (initialModalPosition energyDensity sample) by rfl,
    show initialMassWeightedMomentum energyDensity sample =
      signedFrameReconstruction A
        (initialModalMomentum energyDensity sample) by rfl,
    orderedHarmonicModeEnergy_reconstruction A hsimple]
  have heigen_nonneg : 0 <= orderedEigenvalue A mode := by
    let sampleMass : Unit -> Lattice.PositiveMassConfig N :=
      fun _ => massSample (N := N) sample
    simpa [A, harmonicOrderedEigenvalue, harmonicHermitianSample,
      harmonicHermitian, sampleMass] using
      (harmonicOrderedEigenvalue_nonneg sampleMass () mode)
  by_cases hlast : mode = lastOrderedIndex (ι := Lattice.Site N)
  · subst mode
    have hzero : orderedEigenvalue A
        (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
      simpa [A] using harmonic_lastOrderedEigenvalue_eq_zero
        (massSample (N := N) sample)
    have htarget : orderedModalEnergy N energyDensity
        (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
      rw [lastOrderedIndex_eq_lastSiteOrderedIndex]
      exact orderedModalEnergy_translation_eq_zero energyDensity
    simp [initialModalPosition, initialModalMomentum, orderedFrequency,
      A, hzero, htarget, HarmonicModes.modalEnergy, phaseCoordinate,
      phaseMomentum]
  · have hfrequency : 0 < orderedFrequency sample mode := by
      simpa [orderedFrequency, A] using
        (orderedModeFrequency_pos_iff_ne_last
          (massSample (N := N) sample) hsimple mode).2 hlast
    have htarget : 0 <= orderedModalEnergy N energyDensity mode :=
      orderedModalEnergy_nonneg hN henergyDensity mode
    have hsquare : (orderedFrequency sample mode) ^ 2 =
        orderedEigenvalue A mode := by
      exact Real.sq_sqrt heigen_nonneg
    rw [← hsquare]
    exact modalEnergy_phaseCoordinates _ htarget hfrequency

/-- The same exact energy statement expressed directly in physical `q,p`
coordinates. -/
theorem physicalOrderedModeEnergy_initial_eq_prescribed
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (sample : SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (massSample (N := N) sample)))
    (mode : OrderedMode N) :
    harmonicOrderedPhysicalModeEnergy massSample
        (initialPhysicalPosition energyDensity)
        (initialPhysicalMomentum energyDensity) sample mode =
      orderedModalEnergy N energyDensity mode := by
  rw [harmonicOrderedPhysicalModeEnergy]
  change MeasurableOrderedHarmonicEnergy.orderedHarmonicModeEnergy
      (harmonicHermitian (massSample (N := N) sample)) mode
      (sqrtMassTransform (massSample (N := N) sample)
        (initialPhysicalPosition energyDensity sample))
      (inverseSqrtMassTransform (massSample (N := N) sample)
        (initialPhysicalMomentum energyDensity sample)) = _
  have hposition :
      WithLp.ofLp (sqrtMassTransform (massSample (N := N) sample)
        (initialPhysicalPosition energyDensity sample)) =
        initialMassWeightedPosition energyDensity sample := by
    rw [sqrtMassTransform_initialPhysicalPosition]
  have hmomentum :
      WithLp.ofLp (inverseSqrtMassTransform (massSample (N := N) sample)
        (initialPhysicalMomentum energyDensity sample)) =
        initialMassWeightedMomentum energyDensity sample := by
    rw [inverseSqrtMassTransform_initialPhysicalMomentum]
  rw [hposition, hmomentum]
  exact orderedHarmonicModeEnergy_initial_eq_prescribed hN henergyDensity
    sample hsimple mode

/-- On a simple realization, the sum of all physical ordered modal energies
is exactly the extensive prescribed energy. -/
theorem sum_physicalOrderedModeEnergy_initial_eq_total
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (sample : SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (massSample (N := N) sample))) :
    (∑ mode : OrderedMode N,
      harmonicOrderedPhysicalModeEnergy massSample
        (initialPhysicalPosition energyDensity)
        (initialPhysicalMomentum energyDensity) sample mode) =
      (N : Real) * energyDensity := by
  calc
    _ = ∑ mode : OrderedMode N,
        orderedModalEnergy N energyDensity mode := by
      apply Finset.sum_congr rfl
      intro mode _
      exact physicalOrderedModeEnergy_initial_eq_prescribed hN
        henergyDensity sample hsimple mode
    _ = (N : Real) * energyDensity :=
      sum_orderedModalEnergy_eq_total hN energyDensity

/-- The original-coordinate harmonic Hamiltonian of the constructed physical
state is exactly `N * energyDensity` on a simple realization. -/
theorem physicalHarmonicHamiltonian_initial_eq_total
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (sample : SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (massSample (N := N) sample))) :
    physicalHarmonicHamiltonian (massSample (N := N) sample)
        (CoerciveHamiltonianPhyslib.asConfiguration
          (initialPhysicalMomentum energyDensity sample))
        (CoerciveHamiltonianPhyslib.asConfiguration
          (initialPhysicalPosition energyDensity sample)) =
      (N : Real) * energyDensity := by
  rw [← sum_harmonicOrderedPhysicalModeEnergy_eq_physical_of_simple
    massSample (initialPhysicalPosition energyDensity)
      (initialPhysicalMomentum energyDensity) sample hsimple]
  exact sum_physicalOrderedModeEnergy_initial_eq_total hN henergyDensity
    sample hsimple

/-- Gaussian simple spectrum upgrades the exact per-mode and total physical
energy identities to almost-sure statements. -/
theorem physicalInitialData_energy_spec_ae
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity) :
    ∀ᵐ sample ∂concreteEnsemble.probability,
      (forall mode : OrderedMode N,
        harmonicOrderedPhysicalModeEnergy massSample
            (initialPhysicalPosition energyDensity)
            (initialPhysicalMomentum energyDensity) sample mode =
          orderedModalEnergy N energyDensity mode) ∧
      (∑ mode : OrderedMode N,
        harmonicOrderedPhysicalModeEnergy massSample
          (initialPhysicalPosition energyDensity)
          (initialPhysicalMomentum energyDensity) sample mode) =
        (N : Real) * energyDensity ∧
      physicalHarmonicHamiltonian (massSample (N := N) sample)
          (CoerciveHamiltonianPhyslib.asConfiguration
            (initialPhysicalMomentum energyDensity sample))
          (CoerciveHamiltonianPhyslib.asConfiguration
            (initialPhysicalPosition energyDensity sample)) =
        (N : Real) * energyDensity := by
  filter_upwards [simpleOrderedSpectrum_ae concreteEnsemble
    (N := N) (by omega)] with sample hsimple
  refine ⟨fun mode : OrderedMode N => ?_, ?_, ?_⟩
  · exact physicalOrderedModeEnergy_initial_eq_prescribed hN henergyDensity
      sample hsimple mode
  · exact sum_physicalOrderedModeEnergy_initial_eq_total hN henergyDensity
      sample hsimple
  · exact physicalHarmonicHamiltonian_initial_eq_total hN henergyDensity
      sample hsimple

end

end ArchonPhysics.ConcreteGaussianTwoBandPhysicalInitialData
