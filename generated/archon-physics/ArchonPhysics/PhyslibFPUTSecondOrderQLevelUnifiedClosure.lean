import ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
import ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

/-!
# Q-level unified finite-volume FPUT second-order closure

This module performs one exact replacement in the existing unified
second-order identity: the two observed-child orbit gains together with their
carrier/free feedback corrections are joined into the proved four-copy
q-level signed flux and its placement correction.

The resulting main term consists of the all-distinct noncounterrotating flux,
the repeated-away signed flux, and the observed-child four-copy signed flux.
The all-equal orbit gain remains explicit.  The repeated fixed-point,
observed placement, and all-equal channel-five corrections are displayed
separately, as are the original counterrotating and cross-orbit remainders.

No correction is asserted to vanish.  The inherited finite-volume bounds are
not asserted to be uniform in the lattice size.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

/-! ## Q-level replacement of the observed-child block -/

/-- The previously exposed observed orbit gain plus observed feedback
correction is exactly the new q-level signed flux plus placement correction. -/
theorem observedChildOrbitGain_add_feedbackCorrection_eq_fourSignedFlux_add_placementCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    observedChildOrbitGainSum m kappa time energy observed +
        observedChildFeedbackCorrection m kappa time energy observed =
      observedChildFourSignedFluxSum m kappa time energy observed +
        observedChildPlacementCorrection m kappa time energy observed := by
  have hOld := observedChildContribution_eq_orbitGain_add_correction
    m kappa time energy observed hObserved hEnergy
  have hNew :=
    observedChildA1_add_feedback_eq_fourSignedFlux_add_correction
      m kappa time energy observed hObserved hEnergy
  linear_combination hNew - hOld

/-! ## Explicit q-level main terms -/

/-- Degenerate signed-flux main after resolving both the repeated-away and
observed-child strata. -/
def qLevelDegenerateSignedFluxMain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  repeatedAwaySignedFluxMain m kappa time energy observed +
    observedChildFourSignedFluxSum m kappa time energy observed

/-- Global q-level main: all-distinct noncounterrotating, repeated-away, and
observed-child four-copy signed fluxes, in that order. -/
def qLevelResolvedSecondOrderSignedFluxMain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  allDistinctNoncounterrotatingSignedFluxSum
      m kappa time energy observed +
    repeatedAwaySignedFluxMain m kappa time energy observed +
    observedChildFourSignedFluxSum m kappa time energy observed

/-! ## Degenerate and full exact identities -/

/-- All five degenerate gains and four feedback strata at q level.  The only
remaining orbit gain is all-equal, and all three corrections remain literal. -/
theorem fiveGains_add_fourFeedback_eq_qLevelDegenerateClosure
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
        allEqualChannelFiveCorrection m kappa time energy observed := by
  have hOld := fiveGains_add_fourFeedback_eq_resolvedDegenerateClosure
    m kappa time energy observed hObserved hEnergy
  have hObservedChild :=
    observedChildOrbitGain_add_feedbackCorrection_eq_fourSignedFlux_add_placementCorrection
      m kappa time energy observed hObserved hEnergy
  unfold qLevelDegenerateSignedFluxMain
  unfold degenerateSignedFluxMain degenerateOrbitGainSum
    degenerateTransparentCorrectionSum at hOld
  linear_combination hOld + hObservedChild

/-- Exact full finite-volume second-order formula with the q-level main, the
all-equal orbit gain, all three transparent corrections, and both inherited
remainders shown separately. -/
theorem normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
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
          m kappa time energy observed := by
  have hOld := normalizedSecondOrderHaarBroadening_eq_unifiedClosure
    m kappa beta energy observed htime hObserved hEnergy
  have hObservedChild :=
    observedChildOrbitGain_add_feedbackCorrection_eq_fourSignedFlux_add_placementCorrection
      m kappa time energy observed hObserved hEnergy
  unfold qLevelResolvedSecondOrderSignedFluxMain
  unfold resolvedSecondOrderSignedFluxMain degenerateSignedFluxMain
    degenerateOrbitGainSum degenerateTransparentCorrectionSum at hOld
  linear_combination hOld + hObservedChild

/-! ## Inherited finite-volume bounds -/

/-- The counterrotating remainder keeps exactly its previous inverse-time
bound.  Its static mass is not claimed to be `N`-uniform. -/
theorem abs_qLevelCounterrotatingRemainder_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    |secondOrderCounterrotatingRemainder
        m kappa time energy observed| ≤
      allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
        ((2 / modeFrequency m observed) ^ 2 / time) := by
  exact abs_secondOrderCounterrotatingRemainder_le_inverseTime
    m kappa energy observed htime hObserved hEnergy

/-- The cross-orbit remainder keeps the previous explicit `N^2`
energy-volume bound. -/
theorem abs_qLevelCrossOrbitRemainder_le_energyVolume
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound : Real) (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |secondOrderCrossOrbitRemainder
        m kappa time energy observed| ≤
      2 * (N : Real) ^ 2 * kappa ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time) := by
  exact abs_secondOrderCrossOrbitRemainder_le_energyVolume
    m kappa energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

/-- After subtracting the q-level main, the all-equal orbit gain, all three
corrections, and the counterrotating remainder, only cross-orbit coherence
remains. -/
theorem abs_qLevelUnifiedClosure_sub_counterrotating_le_crossBound
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
        (modeFrequency m observed * time) := by
  have hResidual :
      normalizedSecondOrderHaarBroadening
            m kappa beta energy observed time -
          qLevelResolvedSecondOrderSignedFluxMain
            m kappa time energy observed -
          allEqualOrbitGainSum m kappa time energy observed -
          repeatedAwayFixedPointCorrection m kappa time energy observed -
          observedChildPlacementCorrection m kappa time energy observed -
          allEqualChannelFiveCorrection m kappa time energy observed -
          secondOrderCounterrotatingRemainder
            m kappa time energy observed =
        secondOrderCrossOrbitRemainder
          m kappa time energy observed := by
    rw [normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
      m kappa beta energy observed htime hObserved hEnergy]
    ring
  rw [hResidual]
  exact abs_qLevelCrossOrbitRemainder_le_energyVolume
    m kappa energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

/-- Without subtracting either finite-volume remainder, the inherited bounds
combine by the triangle inequality.  The displayed `N^2` term is retained. -/
theorem abs_qLevelUnifiedClosure_sub_main_le_remainderBounds
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
          (modeFrequency m observed * time) := by
  have hCounter := abs_qLevelCounterrotatingRemainder_le_inverseTime
    m kappa energy observed htime hObserved hEnergy
  have hCross := abs_qLevelCrossOrbitRemainder_le_energyVolume
    m kappa energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved
  have hResidual :
      normalizedSecondOrderHaarBroadening
            m kappa beta energy observed time -
          qLevelResolvedSecondOrderSignedFluxMain
            m kappa time energy observed -
          allEqualOrbitGainSum m kappa time energy observed -
          repeatedAwayFixedPointCorrection m kappa time energy observed -
          observedChildPlacementCorrection m kappa time energy observed -
          allEqualChannelFiveCorrection m kappa time energy observed =
        secondOrderCounterrotatingRemainder
            m kappa time energy observed +
          secondOrderCrossOrbitRemainder
            m kappa time energy observed := by
    rw [normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
      m kappa beta energy observed htime hObserved hEnergy]
    ring
  rw [hResidual]
  exact (abs_add_le _ _).trans (add_le_add hCounter hCross)

end

end ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
