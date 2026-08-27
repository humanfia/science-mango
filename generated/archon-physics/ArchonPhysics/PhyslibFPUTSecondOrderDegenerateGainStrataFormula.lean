import ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
import ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctSignedFluxFormula

/-!
# Exact second-order formula with explicit degenerate A1 gain strata

This module substitutes the five-stratum partition of the positive
non-all-distinct A1 remainder into the exact finite-volume second-order Haar
formula.  The all-distinct signed flux is unchanged.  The positive-inner
non-all-distinct feedback and the real cross-orbit coherent remainder also
remain unchanged and explicit.

This is only an algebraic refinement of an existing exact identity.  It
does not close the degenerate feedback, derive a kinetic equation, or prove
a thermalization limit.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderDegenerateGainStrataFormula

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctSignedFluxFormula
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Exact finite-volume second-order Haar formula after resolving the
positive degenerate A1 gain into five explicit strata.  The remaining
degenerate feedback and cross coherence are not altered. -/
theorem secondOrderBroadening_eq_signedFlux_add_fiveDegenerateGainStrata
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
        positiveInnerNonAllDistinctFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re := by
  rw [secondOrderBroadening_eq_allDistinctSignedFlux_add_remainders
    m kappa beta energy observed htime homega henergy]
  rw [positiveNonAllDistinctRepresentativeA1GainRemainder_eq_five_strata]
  ring

end

end ArchonPhysics.PhyslibFPUTSecondOrderDegenerateGainStrataFormula
