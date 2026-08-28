import ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedClosure
import ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer

/-!
# Resonance-resolved second order with a linear-volume cross bound

For an observed mode written in ordered-spectrum coordinates, simplicity lets
the physical zero-charge cross estimate replace the earlier quadratic-volume
interface in the full resonance-resolved closure.  Only the cross term is
sharpened: the off-resonant and counterrotating static masses remain literal
finite-volume sums, and the potentially resonant correction remains in the
main expression.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedLinearCrossClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory

noncomputable section

/-! ## Deterministic ordered-spectrum endpoint -/

/-- For an ordered observed mode in a simple spectrum, the Physlib cross
remainder is bounded by the physical `O(N / T)` estimate. -/
theorem abs_secondOrderCrossOrbitRemainder_le_linearVolume
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time)
    (hFrequency : 0 < orderedModeFrequency (harmonicHermitian m) q) :
    |secondOrderCrossOrbitRemainder
        m kappa time energy (orderedIndexEquiv q)| ≤
      2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
        (orderedModeFrequency (harmonicHermitian m) q * time) := by
  simpa [secondOrderCrossOrbitRemainder,
    physlibQuadraticCoupling_eq_physicalQuadraticCoupling] using
      (abs_re_physical_crossOrbit_le_energy_linearVolume
        kappa 1 m q energy energyBound hsimple hEnergyBoundNonneg
          hEnergy hEnergyBound hFrequency htime)

/-- Complete fixed-volume resonance-resolved residual estimate with the cross
piece improved from `N^2 / T` to `N / T`.  The first two constants are kept as
their literal, possibly volume-dependent static masses. -/
theorem abs_ordered_resonanceResolvedResidual_le_linearCrossVolumeBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
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
      qLevelOffResonantCorrectionStaticMass
          m kappa energy (orderedIndexEquiv q) / time +
        allDistinctCounterrotatingStaticFluxMass
          m kappa energy (orderedIndexEquiv q) *
          ((2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time) +
        2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
          (orderedModeFrequency (harmonicHermitian m) q * time) := by
  have hObserved : 0 < modeFrequency m (orderedIndexEquiv q) := by
    simpa [orderedModeFrequency_harmonicHermitian_eq] using hFrequency
  have hCross := abs_secondOrderCrossOrbitRemainder_le_linearVolume
    m kappa q energy energyBound hsimple hEnergyBoundNonneg
      hEnergy hEnergyBound htime hFrequency
  have hResidual := abs_resonanceResolvedResidual_le_of_crossBound
    m kappa beta energy (orderedIndexEquiv q) htime hObserved hEnergy hCross
  simpa [orderedModeFrequency_harmonicHermitian_eq] using hResidual

/-! ## Frozen Gaussian leading-mode specialization -/

/-- For the frozen truncated-Gaussian mass ensemble, the complete leading-mode
resonance-resolved estimate holds almost surely.  The two non-cross static
masses remain sample-dependent and explicit. -/
theorem gaussian_ae_abs_leading_resonanceResolvedResidual_le_linearCrossVolumeBound
    {Omega : Type*} [MeasurableSpace Omega]
    {parameters : TruncatedGaussianMassLaw.Parameters}
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
        qLevelOffResonantCorrectionStaticMass
            m kappa energy (orderedIndexEquiv q) / time +
          allDistinctCounterrotatingStaticFluxMass
            m kappa energy (orderedIndexEquiv q) *
            ((2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time) +
          2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
            (Real.sqrt (5 / 3 : Real) * time) := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN]
      with sample hsimple
  let m := ensemble.restrictPositiveMass (N := N) sample
  let q := leadingOrderedModeIndex N
  have hFloor : Real.sqrt (5 / 3 : Real) ≤
      orderedModeFrequency (harmonicHermitian m) q := by
    exact gaussian_leadingOrderedModeFrequency_ge_sqrt_five_thirds
      ensemble hN sample
  have hFrequency : 0 < orderedModeFrequency (harmonicHermitian m) q :=
    (by positivity : 0 < Real.sqrt (5 / 3 : Real)).trans_le hFloor
  have hObserved : 0 < modeFrequency m (orderedIndexEquiv q) := by
    simpa [orderedModeFrequency_harmonicHermitian_eq] using hFrequency
  have hCross := abs_secondOrderCrossOrbitRemainder_le_linearVolume
    m kappa q energy energyBound hsimple hEnergyBoundNonneg
      hEnergy hEnergyBound htime hFrequency
  have hCrossFloor :
      |secondOrderCrossOrbitRemainder
          m kappa time energy (orderedIndexEquiv q)| ≤
        2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
          (Real.sqrt (5 / 3 : Real) * time) := by
    refine hCross.trans ?_
    have hnum :
        0 ≤ 2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 := by
      positivity
    apply div_le_div_of_nonneg_left hnum
    · positivity
    · exact mul_le_mul_of_nonneg_right hFloor htime.le
  have hResidual := abs_resonanceResolvedResidual_le_of_crossBound
    m kappa beta energy (orderedIndexEquiv q) htime hObserved hEnergy
      hCrossFloor
  simpa [orderedModeFrequency_harmonicHermitian_eq] using hResidual

end

end ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedLinearCrossClosure
