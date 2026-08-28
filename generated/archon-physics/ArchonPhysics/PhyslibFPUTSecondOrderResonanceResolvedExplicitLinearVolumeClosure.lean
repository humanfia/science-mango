import ArchonPhysics.FreeFPUTAllDistinctCounterrotatingStaticFluxVolumeBound
import ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedFullLinearVolumeClosure

/-!
# Fully explicit linear-volume resonance-resolved closure

The preceding closure left the all-distinct counterrotating static mass as a
literal finite sum.  The exact fixed-output-to-ordered reindexing and spectral
Parseval estimate now bound that final coefficient linearly in the volume.
Consequently every displayed non-main contribution in the second-order
resonance-resolved residual is explicit `O(N / T)` at a fixed positive output
frequency.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedExplicitLinearVolumeClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingStaticFluxVolumeBound
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedFullLinearVolumeClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TruncatedGaussianMassLaw
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter MeasureTheory

noncomputable section

/-- Deterministic fully explicit residual bound.  The former literal
counterrotating coefficient is replaced by its spectral `O(N)` bound. -/
theorem abs_ordered_resonanceResolvedResidual_le_explicitLinearVolumeBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hCeiling : 0 ≤ ceiling)
    (hFrequencyCeiling : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    (hmassLower : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ (6 / 5 : Real))
    {time : Real} (htime : 0 < time)
    (hFrequency : 0 < orderedModeFrequency (harmonicHermitian m) q) :
    |normalizedSecondOrderHaarBroadening
          m kappa beta energy (orderedIndexEquiv q) time -
        qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy (orderedIndexEquiv q) -
        allEqualOrbitGainSum
          m kappa time energy (orderedIndexEquiv q) -
        qLevelPotentiallyResonantCorrectionSum
          m kappa time energy (orderedIndexEquiv q)| ≤
      (16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          orderedModeFrequency (harmonicHermitian m) q ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          orderedModeFrequency (harmonicHermitian m) q) / time +
        (((3 / 2 : Real) * kappa ^ 2 * ceiling * energyBound ^ 2) *
          (N : Real)) *
          ((2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time) +
        2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
          (orderedModeFrequency (harmonicHermitian m) q * time) := by
  have hbase :=
    abs_ordered_resonanceResolvedResidual_le_fullLinearVolumeBound
      m kappa beta q energy energyBound ceiling hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound hCeiling hFrequencyCeiling
      hmassLower hmassUpper htime hFrequency
  have hcounter := allDistinctCounterrotatingStaticFluxMass_le_linear_volume
    m hsimple kappa energy (orderedIndexEquiv q) energyBound ceiling
      hEnergy hEnergyBound hCeiling hFrequencyCeiling
  have hfactor :
      0 ≤ (2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time :=
    div_nonneg (sq_nonneg _) htime.le
  exact hbase.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcounter hfactor))
    le_rfl)

/-! ## Frozen Gaussian leading-output specialization -/

/-- At the leading ordered mode of every almost-surely simple frozen Gaussian
sample, the complete second-order residual has a fully explicit `O(N/T)`
envelope. -/
theorem gaussian_ae_abs_leading_resonanceResolvedResidual_le_explicitLinearVolumeBound
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa beta : Real) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      let m := ensemble.restrictPositiveMass (N := N) sample
      let q := leadingOrderedModeIndex N
      |normalizedSecondOrderHaarBroadening
            m kappa beta energy (orderedIndexEquiv q) time -
          qLevelResolvedSecondOrderSignedFluxMain
            m kappa time energy (orderedIndexEquiv q) -
          allEqualOrbitGainSum
            m kappa time energy (orderedIndexEquiv q) -
          qLevelPotentiallyResonantCorrectionSum
            m kappa time energy (orderedIndexEquiv q)| ≤
        (16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
          12 * (kappa ^ 2 * energyBound ^ 2 /
            Real.sqrt (5 / 3 : Real) ^ 2) * Real.sqrt 5 +
          8 * kappa ^ 2 * energyBound ^ 2 /
            Real.sqrt (5 / 3 : Real)) / time +
          (((3 / 2 : Real) * kappa ^ 2 * Real.sqrt 5 *
            energyBound ^ 2) * (N : Real)) *
            ((2 / Real.sqrt (5 / 3 : Real)) ^ 2 / time) +
          2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
            (Real.sqrt (5 / 3 : Real) * time) := by
  classical
  filter_upwards
      [gaussian_ae_abs_leading_resonanceResolvedResidual_le_fullLinearVolumeBound
        ensemble hN kappa beta energy energyBound hEnergyBoundNonneg
          hEnergy hEnergyBound htime,
       simpleOrderedSpectrum_ae ensemble hN]
      with sample hbase hsimple
  let m := ensemble.restrictPositiveMass (N := N) sample
  let q := leadingOrderedModeIndex N
  have hfrequencyCeiling : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ Real.sqrt 5 := by
    intro mode
    have h := orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
      m RandomEnsemble.massLower RandomEnsemble.massLower_pos
      (fun i ↦ by
        simpa [m] using (ensemble.mass_mem_support i.val sample).1) mode
    simpa [RandomEnsemble.massLower] using h
  have hcounter := allDistinctCounterrotatingStaticFluxMass_le_linear_volume
    m hsimple kappa energy (orderedIndexEquiv q) energyBound (Real.sqrt 5)
      hEnergy hEnergyBound (Real.sqrt_nonneg _) hfrequencyCeiling
  have hfactor :
      0 ≤ (2 / Real.sqrt (5 / 3 : Real)) ^ 2 / time :=
    div_nonneg (sq_nonneg _) htime.le
  dsimp only at hbase ⊢
  exact hbase.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcounter hfactor))
    le_rfl)

end

end ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedExplicitLinearVolumeClosure
