import ArchonPhysics.FreeFPUTObservedChildAcousticMomentLinearVolumeBound
import ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedLinearCrossClosure
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Resonance-resolved closure with linear-volume q-level and cross terms

This module substitutes the deterministic frozen-support estimate
`M_obs <= N` into the strongest current resonance-resolved second-order
closure.  Thus both the q-level off-resonant contribution and the cross-orbit
contribution have explicit `O(N / T)` envelopes.  The already isolated
all-distinct counterrotating static mass remains literal and transparent; no
volume-uniform estimate for that mass is asserted here.

The frozen Gaussian specialization also discharges the frequency ceiling and
the leading-output frequency floor.  No localization or additional acoustic
gap hypothesis is introduced.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedFullLinearVolumeClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildAcousticMomentLinearVolumeBound
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedLinearCrossClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TruncatedGaussianMassLaw
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter MeasureTheory

noncomputable section

/-- Complete deterministic resonance-resolved residual bound in which both
the q-level off-resonant term and the cross-orbit term have explicit linear
volume dependence.  The counterrotating static mass remains displayed. -/
theorem abs_ordered_resonanceResolvedResidual_le_fullLinearVolumeBound
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
        allDistinctCounterrotatingStaticFluxMass
          m kappa energy (orderedIndexEquiv q) *
          ((2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time) +
        2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
          (orderedModeFrequency (harmonicHermitian m) q * time) := by
  have hObserved : 0 < modeFrequency m (orderedIndexEquiv q) := by
    simpa [orderedModeFrequency_harmonicHermitian_eq] using hFrequency
  have hbase :=
    abs_ordered_resonanceResolvedResidual_le_linearCrossVolumeBound
      m kappa beta q energy energyBound hsimple hEnergyBoundNonneg
      hEnergy hEnergyBound htime hFrequency
  have hoff := qLevelOffResonantCorrectionStaticMass_le_linear_volume
    m kappa energy (orderedIndexEquiv q) energyBound ceiling hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling
      hFrequencyCeiling hmassLower hmassUpper
  have hoffOrdered :
      qLevelOffResonantCorrectionStaticMass
          m kappa energy (orderedIndexEquiv q) ≤
        16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
          12 * (kappa ^ 2 * energyBound ^ 2 /
            orderedModeFrequency (harmonicHermitian m) q ^ 2) * ceiling +
          8 * kappa ^ 2 * energyBound ^ 2 /
            orderedModeFrequency (harmonicHermitian m) q := by
    simpa [orderedModeFrequency_harmonicHermitian_eq] using hoff
  exact hbase.trans (add_le_add
    (add_le_add (div_le_div_of_nonneg_right hoffOrdered htime.le) le_rfl)
    le_rfl)

/-! ## Frozen Gaussian leading-output specialization -/

/-- Frozen Gaussian leading-output endpoint.  The q-level and cross-orbit
pieces are now explicit `O(N/T)` expressions; the only remaining unbounded
finite-volume coefficient is the displayed counterrotating static mass. -/
theorem gaussian_ae_abs_leading_resonanceResolvedResidual_le_fullLinearVolumeBound
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
          allDistinctCounterrotatingStaticFluxMass
            m kappa energy (orderedIndexEquiv q) *
            ((2 / Real.sqrt (5 / 3 : Real)) ^ 2 / time) +
          2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
            (Real.sqrt (5 / 3 : Real) * time) := by
  classical
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN]
      with sample hsimple
  let m := ensemble.restrictPositiveMass (N := N) sample
  let q := leadingOrderedModeIndex N
  let omega := orderedModeFrequency (harmonicHermitian m) q
  let omegaFloor := Real.sqrt (5 / 3 : Real)
  have hFloor : omegaFloor ≤ omega := by
    exact gaussian_leadingOrderedModeFrequency_ge_sqrt_five_thirds
      ensemble hN sample
  have hFloorPositive : 0 < omegaFloor := by
    dsimp only [omegaFloor]
    positivity
  have hFrequency : 0 < omega := hFloorPositive.trans_le hFloor
  have hFrequencyCeiling : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ Real.sqrt 5 :=
    fun mode ↦ by
      have h := orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
        m RandomEnsemble.massLower RandomEnsemble.massLower_pos
        (fun i ↦ by
          simpa [m] using (ensemble.mass_mem_support i.val sample).1) mode
      simpa [RandomEnsemble.massLower] using h
  have hmassLower : ∀ i, (4 / 5 : Real) ≤ m.mass i := by
    intro i
    simpa [m, RandomEnsemble.massLower] using
      (ensemble.mass_mem_support i.val sample).1
  have hmassUpper : ∀ i, m.mass i ≤ (6 / 5 : Real) := by
    intro i
    simpa [m, RandomEnsemble.massUpper] using
      (ensemble.mass_mem_support i.val sample).2
  have hbase :=
    abs_ordered_resonanceResolvedResidual_le_fullLinearVolumeBound
      m kappa beta q energy energyBound (Real.sqrt 5) hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound (Real.sqrt_nonneg 5)
      hFrequencyCeiling hmassLower hmassUpper htime hFrequency
  have hFrequencySq : omegaFloor ^ 2 ≤ omega ^ 2 := by
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hFloor 2
  have henergyFactor : 0 ≤ kappa ^ 2 * energyBound ^ 2 := by positivity
  have hdivSq :
      kappa ^ 2 * energyBound ^ 2 / omega ^ 2 ≤
        kappa ^ 2 * energyBound ^ 2 / omegaFloor ^ 2 := by
    exact div_le_div_of_nonneg_left henergyFactor
      (sq_pos_of_pos hFloorPositive) hFrequencySq
  have hdiv :
      kappa ^ 2 * energyBound ^ 2 / omega ≤
        kappa ^ 2 * energyBound ^ 2 / omegaFloor := by
    exact div_le_div_of_nonneg_left henergyFactor hFloorPositive hFloor
  have htwoDiv : 2 / omega ≤ 2 / omegaFloor := by
    exact div_le_div_of_nonneg_left (by norm_num) hFloorPositive hFloor
  have htwoDivSq : (2 / omega) ^ 2 ≤ (2 / omegaFloor) ^ 2 := by
    exact pow_le_pow_left₀ (div_nonneg (by norm_num) hFrequency.le)
      htwoDiv 2
  have hcrossNumerator :
      0 ≤ 2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 := by
    positivity
  have hcross :
      2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 / (omega * time) ≤
        2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
          (omegaFloor * time) := by
    exact div_le_div_of_nonneg_left hcrossNumerator
      (mul_pos hFloorPositive htime) (mul_le_mul_of_nonneg_right hFloor htime.le)
  have hcounterMass : 0 ≤ allDistinctCounterrotatingStaticFluxMass
      m kappa energy (orderedIndexEquiv q) := by
    unfold allDistinctCounterrotatingStaticFluxMass
    apply Finset.sum_nonneg
    intro term hterm
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg kappa)
          (normalizedInteractionWeight_nonneg m
            (quadraticCollisionModes (orderedIndexEquiv q) term))))
      (quadraticSignedCollisionFlux_nonneg_of_counterrotating
        m energy (orderedIndexEquiv q) term hEnergy
          (Finset.mem_filter.mp hterm).2)
  dsimp only at hbase ⊢
  exact hbase.trans (add_le_add
    (add_le_add
      (div_le_div_of_nonneg_right (by gcongr) htime.le)
      (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right htwoDivSq htime.le) hcounterMass))
    hcross)

end

end ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedFullLinearVolumeClosure
