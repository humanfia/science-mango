import ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedClosure

/-!
# Consumer: full second-order resonance-resolved FPUT closure

The dangerous q-level correction sectors remain explicit in the main formula.
Only off-resonant corrections, the counterrotating remainder, and cross-orbit
coherence enter the residual estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

/-- Consumer-facing exact full resonance-resolved second-order formula. -/
theorem problem_normalizedSecondOrderHaarBroadening_eq_resonanceResolvedClosure
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time =
      qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy observed +
        allEqualOrbitGainSum m kappa time energy observed +
        qLevelPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        qLevelOffResonantCorrectionSum
          m kappa time energy observed +
        secondOrderCounterrotatingRemainder
          m kappa time energy observed +
        secondOrderCrossOrbitRemainder
          m kappa time energy observed :=
  normalizedSecondOrderHaarBroadening_eq_resonanceResolvedClosure
    m kappa beta energy observed htime hObserved hEnergy

/-- Replaceable cross-bound composition endpoint. -/
theorem problem_abs_resonanceResolvedResidual_le_of_crossBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time crossBound : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hCross : |secondOrderCrossOrbitRemainder
      m kappa time energy observed| ≤ crossBound) :
    |normalizedSecondOrderHaarBroadening
          m kappa beta energy observed time -
        qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy observed -
        allEqualOrbitGainSum m kappa time energy observed -
        qLevelPotentiallyResonantCorrectionSum
          m kappa time energy observed| ≤
      qLevelOffResonantCorrectionStaticMass
          m kappa energy observed / time +
        allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
          ((2 / modeFrequency m observed) ^ 2 / time) +
        crossBound :=
  abs_resonanceResolvedResidual_le_of_crossBound
    m kappa beta energy observed htime hObserved hEnergy hCross

/-- Current concrete total residual bound, using the committed `N^2 / T`
cross estimate through its named interface. -/
theorem problem_abs_resonanceResolvedResidual_le_currentFiniteVolumeBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound : Real) (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |normalizedSecondOrderHaarBroadening
          m kappa beta energy observed time -
        qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy observed -
        allEqualOrbitGainSum m kappa time energy observed -
        qLevelPotentiallyResonantCorrectionSum
          m kappa time energy observed| ≤
      currentResonanceResolvedResidualBound
        m kappa energy observed energyBound time :=
  abs_resonanceResolvedResidual_le_currentFiniteVolumeBound
    m kappa beta energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

#print axioms
  problem_normalizedSecondOrderHaarBroadening_eq_resonanceResolvedClosure
#print axioms problem_abs_resonanceResolvedResidual_le_of_crossBound
#print axioms
  problem_abs_resonanceResolvedResidual_le_currentFiniteVolumeBound

end

end ArchonPhysicsConsumers.Thermalization
