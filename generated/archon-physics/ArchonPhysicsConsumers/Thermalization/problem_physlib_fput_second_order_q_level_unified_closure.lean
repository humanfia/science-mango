import ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure

/-!
# Consumer: q-level unified FPUT second-order closure

The observed-child orbit gains and feedback corrections are now replaced by
their four-copy signed flux and exact placement correction.  The all-equal
orbit gain, all three corrections, counterrotating remainder, cross-orbit
remainder, and non-uniform finite-volume bounds remain explicit.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

theorem problem_fiveGains_add_fourFeedback_eq_qLevelDegenerateClosure
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    fiveDegenerateGainStrataSum m kappa time energy observed +
        fourDegenerateFeedbackStrataSum m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      qLevelDegenerateSignedFluxMain m kappa time energy observed +
        allEqualOrbitGainSum m kappa time energy observed +
        repeatedAwayFixedPointCorrection m kappa time energy observed +
        observedChildPlacementCorrection m kappa time energy observed +
        allEqualChannelFiveCorrection m kappa time energy observed :=
  fiveGains_add_fourFeedback_eq_qLevelDegenerateClosure
    m kappa time energy observed hObserved hEnergy

theorem problem_normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
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
        repeatedAwayFixedPointCorrection m kappa time energy observed +
        observedChildPlacementCorrection m kappa time energy observed +
        allEqualChannelFiveCorrection m kappa time energy observed +
        secondOrderCounterrotatingRemainder
          m kappa time energy observed +
        secondOrderCrossOrbitRemainder
          m kappa time energy observed :=
  normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
    m kappa beta energy observed htime hObserved hEnergy

theorem problem_abs_qLevelUnifiedClosure_sub_counterrotating_le_crossBound
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
        repeatedAwayFixedPointCorrection m kappa time energy observed -
        observedChildPlacementCorrection m kappa time energy observed -
        allEqualChannelFiveCorrection m kappa time energy observed -
        secondOrderCounterrotatingRemainder
          m kappa time energy observed| ≤
      2 * (N : Real) ^ 2 * kappa ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time) :=
  abs_qLevelUnifiedClosure_sub_counterrotating_le_crossBound
    m kappa beta energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

theorem problem_abs_qLevelUnifiedClosure_sub_main_le_remainderBounds
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
        repeatedAwayFixedPointCorrection m kappa time energy observed -
        observedChildPlacementCorrection m kappa time energy observed -
        allEqualChannelFiveCorrection m kappa time energy observed| ≤
      allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
          ((2 / modeFrequency m observed) ^ 2 / time) +
        2 * (N : Real) ^ 2 * kappa ^ 2 * energyBound ^ 2 /
          (modeFrequency m observed * time) :=
  abs_qLevelUnifiedClosure_sub_main_le_remainderBounds
    m kappa beta energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

#print axioms problem_fiveGains_add_fourFeedback_eq_qLevelDegenerateClosure
#print axioms
  problem_normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
#print axioms
  problem_abs_qLevelUnifiedClosure_sub_counterrotating_le_crossBound
#print axioms
  problem_abs_qLevelUnifiedClosure_sub_main_le_remainderBounds

end

end ArchonPhysicsConsumers.Thermalization
