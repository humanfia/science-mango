import ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
import ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
import ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
import ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex
import ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound

/-!
# Unified finite-volume second-order degenerate closure

This module combines the complete five-gain/four-feedback decomposition with
the three proved global degenerate closures.  It keeps every term visible:

* repeated-away terms become signed flux plus the fixed-point correction;
* observed-child gains remain explicit orbit gains, while their carrier and
  free feedback become two explicit corrections;
* the all-equal orbit gain and surviving selector-five correction remain
  separate;
* the all-distinct counterrotating sector and cross-orbit coherence remain
  finite-volume remainders with their previously proved bounds.

No correction is asserted to vanish, and none of the displayed estimates is
asserted to be uniform in the lattice size.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge
open ArchonPhysics.SignedThreeWaveCollisionFlux

noncomputable section

/-! ## Explicit pieces of the degenerate closure -/

/-- Signed-flux part of the repeated-away stratum.  Same-sign fixed points
carry one signed-flux copy; the opposite-sign sector carries the proved four
copies. -/
def repeatedAwaySignedFluxMain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  (∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
    finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q) *
      quadraticSignedCollisionFlux q
        (modeAction energy (modeFrequency m)) observed) +
    ∑ q ∈ positiveRepeatedChildOppositeSignRepresentatives N m observed,
      repeatedChildOppositeSignFourSignedFlux
        m kappa time energy observed q

/-- The exact two-copy correction retained by the same-sign fixed-point
sector. -/
def repeatedAwayFixedPointCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
    2 * finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q) *
      (quadraticInputInteractionSign q 0).coefficient *
      modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m) (q.1 0)

/-- The two observed-child A1 orbit gains. -/
def observedChildOrbitGainSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  positiveObservedOnlyAtChildZeroRepresentativeA1Gain
      m kappa time energy observed +
    positiveObservedOnlyAtChildOneRepresentativeA1Gain
      m kappa time energy observed

/-- The two globally reindexed observed-child feedback corrections.  The
carrier contribution has four placements and the free contribution has the
proved two-placement collapse. -/
def observedChildFeedbackCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  observedCarrierSignedKernelSum m kappa time energy observed +
    observedFreeCollapsedKernelSum m kappa time energy observed

/-- Explicit all-equal A1 orbit gain. -/
def allEqualOrbitGainSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveObservedAtBothChildrenRepresentatives N m observed,
    ((quadraticSwapOrbit q).card : Real) ^ 2 *
      finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q) *
      modeAction energy (modeFrequency m) observed ^ 2

/-- Surviving all-equal selector-five correction with its proved canonical
multiplicity. -/
def allEqualChannelFiveCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
    (quadraticInputInteractionSign parameter.1
        parameter.2.1).coefficient *
      finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign parameter.1) time
        (quadraticCollisionModes observed parameter.1) *
      modeAction energy (modeFrequency m) observed ^ 2

/-- All signed-flux terms created by closing the repeated-away degenerate
stratum. -/
def degenerateSignedFluxMain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  repeatedAwaySignedFluxMain m kappa time energy observed

/-- Orbit gains that remain after all four feedback strata are globally
resolved. -/
def degenerateOrbitGainSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  observedChildOrbitGainSum m kappa time energy observed +
    allEqualOrbitGainSum m kappa time energy observed

/-- Complete transparent correction list.  No summand is claimed to vanish:
the list consists of the repeated fixed-point, observed carrier, observed
free, and all-equal channel-five corrections. -/
def degenerateTransparentCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  repeatedAwayFixedPointCorrection m kappa time energy observed +
    observedChildFeedbackCorrection m kappa time energy observed +
    allEqualChannelFiveCorrection m kappa time energy observed

/-! ## The five-gain/four-feedback closure -/

/-- The repeated-away closure with its fixed-point correction separated from
the signed-flux main term. -/
theorem repeatedAwayContribution_eq_main_add_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveRepeatedChildSameSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveRepeatedChildOppositeSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      repeatedAwaySignedFluxMain m kappa time energy observed +
        repeatedAwayFixedPointCorrection m kappa time energy observed := by
  rw [repeatedAwayRepresentativeA1Gain_add_feedback_eq_signedFlux
    m kappa time energy observed hObserved hEnergy]
  unfold repeatedAwaySignedFluxMain repeatedAwayFixedPointCorrection
    repeatedChildSameSignSignedFluxWithCorrection
  rw [Finset.sum_add_distrib]
  ring

/-- Exact observed-child closure, retaining both orbit gains and both
globally reindexed feedback corrections. -/
theorem observedChildContribution_eq_orbitGain_add_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveObservedOnlyAtChildZeroRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildOneRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerObservedOnlyAtCarrierFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        positiveInnerObservedOnlyAtFreeFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      observedChildOrbitGainSum m kappa time energy observed +
        observedChildFeedbackCorrection m kappa time energy observed := by
  rw [observedChildA1_add_feedback_eq_resolved
    m kappa time energy observed hObserved hEnergy]
  unfold observedChildOrbitGainSum observedChildFeedbackCorrection
  ring

/-- Exact all-equal closure into its orbit gain and selector-five
correction. -/
theorem allEqualContribution_eq_orbitGain_add_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveObservedAtBothChildrenRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerObservedAtCarrierAndFreeFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      allEqualOrbitGainSum m kappa time energy observed +
        allEqualChannelFiveCorrection m kappa time energy observed := by
  rw [allEqualRepresentativeA1Gain_add_feedback_eq_signedParameters
    m kappa time energy observed hEnergy]
  unfold allEqualOrbitGainSum allEqualChannelFiveCorrection
  rfl

/-- Unified replacement of all five degenerate A1 gains and all four
degenerate feedback strata. -/
theorem fiveGains_add_fourFeedback_eq_resolvedDegenerateClosure
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
          m kappa time energy observed := by
  have hRepeated := repeatedAwayContribution_eq_main_add_correction
    m kappa time energy observed hObserved hEnergy
  have hObservedChild := observedChildContribution_eq_orbitGain_add_correction
    m kappa time energy observed hObserved hEnergy
  have hAllEqual := allEqualContribution_eq_orbitGain_add_correction
    m kappa time energy observed hEnergy
  unfold fiveDegenerateGainStrataSum fourDegenerateFeedbackStrataSum
    degenerateSignedFluxMain degenerateOrbitGainSum
    degenerateTransparentCorrectionSum
  linear_combination hRepeated + hObservedChild + hAllEqual

/-! ## Full second-order formula and finite-volume remainder bounds -/

/-- Noncounterrotating all-distinct flux together with the resolved
degenerate signed flux. -/
def resolvedSecondOrderSignedFluxMain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  allDistinctNoncounterrotatingSignedFluxSum
      m kappa time energy observed +
    degenerateSignedFluxMain m kappa time energy observed

/-- The all-distinct all-plus sector, retained as a finite-volume
counterrotating remainder. -/
def secondOrderCounterrotatingRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  allDistinctCounterrotatingSignedFluxSum
    m kappa time energy observed

/-- Cross-swap-orbit coherent remainder from the exact Haar formula. -/
def secondOrderCrossOrbitRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  (freeQuadraticCrossSwapOrbitCoherentRemainder
    (physlibQuadraticCoupling m kappa 1 observed) m observed
    (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
    time).re

/-- Exact unified finite-volume second-order formula.  Both remainders and
all four transparent corrections remain displayed. -/
theorem normalizedSecondOrderHaarBroadening_eq_unifiedClosure
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
          m kappa time energy observed := by
  calc
    normalizedSecondOrderHaarBroadening
          m kappa beta energy observed time =
        allDistinctRepresentativeSignedFluxSum
            m kappa time energy observed +
          fiveDegenerateGainStrataSum m kappa time energy observed +
          fourDegenerateFeedbackStrataSum m kappa time
            (phaseEnergyRadius energy (modeFrequency m)) observed +
          secondOrderCrossOrbitRemainder
            m kappa time energy observed := by
      simpa [secondOrderCrossOrbitRemainder] using
        (normalizedSecondOrderHaarBroadening_eq_resolvedStrata_add_cross
          m kappa beta energy observed htime hObserved hEnergy)
    _ = _ := by
      have hDegenerate :=
        fiveGains_add_fourFeedback_eq_resolvedDegenerateClosure
          m kappa time energy observed hObserved hEnergy
      rw [allDistinctRepresentativeSignedFluxSum_eq_noncounterrotating_add_counterrotating]
      unfold resolvedSecondOrderSignedFluxMain
        secondOrderCounterrotatingRemainder
      linear_combination hDegenerate

/-- The counterrotating remainder retains its proved fixed-volume
inverse-time bound.  The static mass is not claimed to be `N`-uniform. -/
theorem abs_secondOrderCounterrotatingRemainder_le_inverseTime
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
  exact abs_allDistinctCounterrotatingSignedFluxSum_le_inverseTime
    m kappa energy observed htime hObserved hEnergy

/-- The cross-orbit remainder retains the proved physical energy-volume
bound.  Its explicit `N^2` factor is intentionally not hidden. -/
theorem abs_secondOrderCrossOrbitRemainder_le_energyVolume
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
  simpa [secondOrderCrossOrbitRemainder,
    physlibQuadraticCoupling_eq_physicalQuadraticCoupling] using
      (abs_re_physical_crossOrbit_le_energy_volume
        kappa 1 m observed energy energyBound hEnergyBoundNonneg
        hEnergy hEnergyBound hObserved htime)

/-- After subtracting the main flux, orbit gains, transparent corrections,
and the counterrotating remainder, only cross-orbit coherence remains. -/
theorem abs_unifiedClosure_sub_counterrotating_le_crossBound
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
        (modeFrequency m observed * time) := by
  have hResidual :
      normalizedSecondOrderHaarBroadening
            m kappa beta energy observed time -
          resolvedSecondOrderSignedFluxMain m kappa time energy observed -
          degenerateOrbitGainSum m kappa time energy observed -
          degenerateTransparentCorrectionSum m kappa time energy observed -
          secondOrderCounterrotatingRemainder
            m kappa time energy observed =
        secondOrderCrossOrbitRemainder
          m kappa time energy observed := by
    rw [normalizedSecondOrderHaarBroadening_eq_unifiedClosure
      m kappa beta energy observed htime hObserved hEnergy]
    ring
  rw [hResidual]
  exact abs_secondOrderCrossOrbitRemainder_le_energyVolume
    m kappa energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

/-- If neither remainder is subtracted, their two proved finite-volume bounds
combine by the triangle inequality.  This is not an `N`-uniform estimate. -/
theorem abs_unifiedClosure_sub_main_le_remainderBounds
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
          (modeFrequency m observed * time) := by
  have hCounter := abs_secondOrderCounterrotatingRemainder_le_inverseTime
    m kappa energy observed htime hObserved hEnergy
  have hCross := abs_secondOrderCrossOrbitRemainder_le_energyVolume
    m kappa energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved
  have hResidual :
      normalizedSecondOrderHaarBroadening
            m kappa beta energy observed time -
          resolvedSecondOrderSignedFluxMain m kappa time energy observed -
          degenerateOrbitGainSum m kappa time energy observed -
          degenerateTransparentCorrectionSum m kappa time energy observed =
        secondOrderCounterrotatingRemainder
            m kappa time energy observed +
          secondOrderCrossOrbitRemainder
            m kappa time energy observed := by
    rw [normalizedSecondOrderHaarBroadening_eq_unifiedClosure
      m kappa beta energy observed htime hObserved hEnergy]
    ring
  rw [hResidual]
  exact (abs_add_le _ _).trans (add_le_add hCounter hCross)

end

end ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
