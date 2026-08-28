import ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound
import ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Gaussian leading-output consumer for q-level off-resonant corrections

On the frozen Gaussian random-mass ensemble, simplicity holds almost surely,
the leading output frequency has a deterministic positive floor, and every
mode frequency is at most `sqrt 5`.  The q-level off-resonant remainder is
therefore `1 / time` times one explicit acoustic moment plus three genuinely
volume-independent terms.
-/

namespace ArchonPhysics.PhyslibFPUTGaussianQLevelOffResonantVolumeConsumer

open ArchonPhysics
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTQLevelOffResonantVolumeBound
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TruncatedGaussianMassLaw
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter MeasureTheory

noncomputable section

/-- Almost-sure leading-output endpoint.  The only term whose volume behavior
is not settled by orthogonality is the displayed acoustic moment `M_obs`;
there is no hidden minimum-frequency constant. -/
theorem gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa : Real) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (hTime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      let m := ensemble.restrictPositiveMass (N := N) sample
      let q := leadingOrderedModeIndex N
      let observed := orderedIndexEquiv q
      |qLevelOffResonantCorrectionSum
          m kappa time energy observed| ≤
        (16 * kappa ^ 2 * energyBound ^ 2 *
            observedChildAcousticInverseMoment m observed +
          12 * (kappa ^ 2 * energyBound ^ 2 /
            modeFrequency m observed ^ 2) * Real.sqrt 5 +
          8 * kappa ^ 2 * energyBound ^ 2 /
            modeFrequency m observed) / time := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN]
      with sample hsimple
  let m := ensemble.restrictPositiveMass (N := N) sample
  let q := leadingOrderedModeIndex N
  let observed := orderedIndexEquiv q
  have hfloor : Real.sqrt (5 / 3 : Real) ≤
      orderedModeFrequency (harmonicHermitian m) q :=
    gaussian_leadingOrderedModeFrequency_ge_sqrt_five_thirds
      ensemble hN sample
  have hObservedOrdered : 0 <
      orderedModeFrequency (harmonicHermitian m) q :=
    (by positivity : 0 < Real.sqrt (5 / 3 : Real)).trans_le hfloor
  have hObserved : 0 < modeFrequency m observed := by
    simpa [observed, orderedModeFrequency_harmonicHermitian_eq] using
      hObservedOrdered
  have hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ Real.sqrt 5 :=
    fun mode ↦ by
      have h := orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
        m RandomEnsemble.massLower RandomEnsemble.massLower_pos
        (fun i ↦ by
          simpa [m] using (ensemble.mass_mem_support i.val sample).1) mode
      simpa [RandomEnsemble.massLower] using h
  dsimp only
  exact
    abs_qLevelOffResonantCorrectionSum_le_acousticMoment_add_uniform_over_time
      m kappa energy observed energyBound (Real.sqrt 5) hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound hObserved
      (Real.sqrt_nonneg 5) hFrequency hTime

/-- The same frozen-Gaussian endpoint after discharging the acoustic moment
with the unconditional finite-cycle Poincare floor.  The resulting
`N^(3/2) / time` envelope is coarse but fully explicit and contains no hidden
minimum-frequency, localization, or acoustic hypothesis. -/
theorem gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le_explicit
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa : Real) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (hTime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      let m := ensemble.restrictPositiveMass (N := N) sample
      let q := leadingOrderedModeIndex N
      let observed := orderedIndexEquiv q
      |qLevelOffResonantCorrectionSum
          m kappa time energy observed| ≤
        (16 * kappa ^ 2 * energyBound ^ 2 *
            Real.sqrt
              (4 * RandomEnsemble.massUpper * (N : Real) ^ 3) +
          12 * (kappa ^ 2 * energyBound ^ 2 /
            modeFrequency m observed ^ 2) * Real.sqrt 5 +
          8 * kappa ^ 2 * energyBound ^ 2 /
            modeFrequency m observed) / time := by
  filter_upwards
      [gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le
        ensemble hN kappa energy energyBound hEnergyBoundNonneg
          hEnergy hEnergyBound hTime]
      with sample hbase
  let m := ensemble.restrictPositiveMass (N := N) sample
  let q := leadingOrderedModeIndex N
  let observed := orderedIndexEquiv q
  have hmoment : observedChildAcousticInverseMoment m observed ≤
      Real.sqrt (4 * RandomEnsemble.massUpper * (N : Real) ^ 3) := by
    exact observedChildAcousticInverseMoment_le_explicit_sqrt
      m RandomEnsemble.massUpper
      (RandomEnsemble.massLower_pos.trans_le
        RandomEnsemble.massLower_le_massUpper)
      (fun i ↦ by
        simpa [m] using (ensemble.mass_mem_support i.val sample).2)
      observed
  dsimp only at hbase ⊢
  exact hbase.trans (div_le_div_of_nonneg_right (by
    gcongr) hTime.le)

end

end ArchonPhysics.PhyslibFPUTGaussianQLevelOffResonantVolumeConsumer
