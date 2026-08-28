import ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

/-!
# Consumer: unified finite-volume second-order degenerate closure

The five degenerate A1 gains and four feedback strata are replaced by the
proved signed-flux, orbit-gain, and transparent-correction pieces.  The
counterrotating and cross-orbit terms remain explicit finite-volume
remainders with non-uniform bounds.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

theorem problem_fiveGains_add_fourFeedback_eq_resolvedDegenerateClosure
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    fiveDegenerateGainStrataSum m kappa time energy observed +
        fourDegenerateFeedbackStrataSum m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      degenerateSignedFluxMain m kappa time energy observed +
        degenerateOrbitGainSum m kappa time energy observed +
        degenerateTransparentCorrectionSum
          m kappa time energy observed :=
  fiveGains_add_fourFeedback_eq_resolvedDegenerateClosure
    m kappa time energy observed hObserved hEnergy

theorem problem_normalizedSecondOrderHaarBroadening_eq_unifiedClosure
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time =
      resolvedSecondOrderSignedFluxMain
          m kappa time energy observed +
        degenerateOrbitGainSum m kappa time energy observed +
        degenerateTransparentCorrectionSum
          m kappa time energy observed +
        secondOrderCounterrotatingRemainder
          m kappa time energy observed +
        secondOrderCrossOrbitRemainder
          m kappa time energy observed :=
  normalizedSecondOrderHaarBroadening_eq_unifiedClosure
    m kappa beta energy observed htime hObserved hEnergy

theorem problem_abs_unifiedClosure_sub_counterrotating_le_crossBound
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
        resolvedSecondOrderSignedFluxMain m kappa time energy observed -
        degenerateOrbitGainSum m kappa time energy observed -
        degenerateTransparentCorrectionSum m kappa time energy observed -
        secondOrderCounterrotatingRemainder
          m kappa time energy observed| ≤
      2 * (N : Real) ^ 2 * kappa ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time) :=
  abs_unifiedClosure_sub_counterrotating_le_crossBound
    m kappa beta energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

theorem problem_abs_unifiedClosure_sub_main_le_remainderBounds
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
        resolvedSecondOrderSignedFluxMain m kappa time energy observed -
        degenerateOrbitGainSum m kappa time energy observed -
        degenerateTransparentCorrectionSum m kappa time energy observed| ≤
      allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
          ((2 / modeFrequency m observed) ^ 2 / time) +
        2 * (N : Real) ^ 2 * kappa ^ 2 * energyBound ^ 2 /
          (modeFrequency m observed * time) :=
  abs_unifiedClosure_sub_main_le_remainderBounds
    m kappa beta energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

#print axioms problem_fiveGains_add_fourFeedback_eq_resolvedDegenerateClosure
#print axioms problem_normalizedSecondOrderHaarBroadening_eq_unifiedClosure
#print axioms problem_abs_unifiedClosure_sub_counterrotating_le_crossBound
#print axioms problem_abs_unifiedClosure_sub_main_le_remainderBounds

end

end ArchonPhysicsConsumers.Thermalization
