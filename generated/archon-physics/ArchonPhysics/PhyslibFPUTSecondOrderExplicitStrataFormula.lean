import ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
import ArchonPhysics.PhyslibFPUTSecondOrderDegenerateGainStrataFormula

/-!
# Exact second-order formula with explicit gain and feedback strata

This module expands the remaining aggregate positive-inner degenerate
feedback in the five-gain-stratum second-order Haar formula.  The resulting
identity displays the all-distinct signed flux, five positive degenerate A1
gain strata, four intrinsic matched-tree feedback strata, and the real part
of the cross-orbit coherent remainder.

The four feedback strata are only partitioned, not evaluated.  No local
constructor multiplicity, degenerate gain--loss closure, kinetic limit, or
thermalization conclusion is asserted.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderExplicitStrataFormula

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderDegenerateGainStrataFormula
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Exact finite-volume F2 strata formula.  Every positive degenerate A1
gain and every positive-inner degenerate feedback tree appears in one named
stratum, while cross-orbit coherence remains as its exact real remainder. -/
theorem secondOrderBroadening_eq_explicitGainFeedbackStrata
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    (1 / time) *
      (∫ phase : UnitAddTorus (Lattice.Site N),
        twoStepSecondCoefficient
          (canonicalFreeComplexInitialAmplitude
            (phaseEnergyRadius energy (modeFrequency m))
            (modeFrequency m) phase observed)
          (physlibQuadraticFirstPicardCoefficient m kappa
            (phaseEnergyRadius energy (modeFrequency m)) phase time observed)
          (physlibFPUTSecondPicardCoefficient m kappa beta observed
            (phaseEnergyRadius energy (modeFrequency m)) phase time)
        ∂finitePhaseHaarLaw (Lattice.Site N)) =
      allDistinctRepresentativeSignedFluxSum
          m kappa time energy observed +
        positiveRepeatedChildSameSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveRepeatedChildOppositeSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildZeroRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildOneRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedAtBothChildrenRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        positiveInnerObservedOnlyAtCarrierFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        positiveInnerObservedOnlyAtFreeFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        positiveInnerObservedAtCarrierAndFreeFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re := by
  rw [secondOrderBroadening_eq_signedFlux_add_fiveDegenerateGainStrata
    m kappa beta energy observed htime homega henergy]
  rw [positiveInnerNonAllDistinctFeedbackRemainder_eq_four_strata]
  ring

end

end ArchonPhysics.PhyslibFPUTSecondOrderExplicitStrataFormula
