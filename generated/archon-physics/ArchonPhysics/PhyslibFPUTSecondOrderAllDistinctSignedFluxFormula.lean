import ArchonPhysics.FreeFPUTAllDistinctGlobalConnectedFeedbackReindex
import ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
import ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctGainPartition

/-!
# Exact all-distinct signed-flux formula with explicit remainders

This module closes the positive all-distinct sector of the original
finite-volume second-order Haar formula.  The coherent A1 gain and the full
all-distinct connected-return feedback are replaced exactly by the canonical
representative signed three-wave collision sum.

Every term outside that sector remains explicit:

* positive but mode-degenerate A1 representatives;
* positive-inner non-all-distinct return feedback;
* the real part of the zero-charge cross-swap-orbit coherent remainder.

No kinetic limit, random-phase approximation, counterrotating deletion, or
nonlinear remainder estimate is used.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctSignedFluxFormula

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTAllDistinctGlobalConnectedFeedbackReindex
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
open ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctGainPartition
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Exact finite-volume formula: the complete positive all-distinct sector is
the signed collision sum, and all complementary terms are displayed. -/
theorem secondOrderBroadening_eq_allDistinctSignedFlux_add_remainders
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
        positiveNonAllDistinctRepresentativeA1GainRemainder
          m kappa time energy observed +
        positiveInnerNonAllDistinctFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re := by
  rw [normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_allDistinctGain_add_remainders
    m kappa beta energy observed htime homega henergy]
  rw [positiveInnerCompactFeedbackSum_eq_allDistinct_add_remainder]
  rw [sum_positiveInnerAllDistinctConnectedFeedback_eq_representative
    m kappa time energy observed homega]
  have hClosure :=
    allDistinctRepresentativeGain_add_feedback_eq_signedFluxSum
      m kappa time energy observed henergy
  calc
    _ = (allDistinctRepresentativeA1GainSum
            m kappa time energy observed +
          allDistinctRepresentativeConnectedFeedbackSum
            m kappa time energy observed) +
        positiveNonAllDistinctRepresentativeA1GainRemainder
          m kappa time energy observed +
        positiveInnerNonAllDistinctFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re := by ring
    _ = _ := by rw [hClosure]

end

end ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctSignedFluxFormula
