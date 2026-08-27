import ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctErrorBound

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
open ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
open ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctErrorBound
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer-facing fixed-volume inverse-time error certificate for the
resolved all-distinct second-order formula. -/
theorem problem_abs_secondOrderBroadening_sub_resolvedTerms_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    |(1 / time) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          twoStepSecondCoefficient
            (canonicalFreeComplexInitialAmplitude
              (phaseEnergyRadius energy (modeFrequency m))
              (modeFrequency m) phase observed)
            (physlibQuadraticFirstPicardCoefficient m kappa
              (phaseEnergyRadius energy (modeFrequency m)) phase time observed)
            (physlibFPUTSecondPicardCoefficient m kappa beta observed
              (phaseEnergyRadius energy (modeFrequency m)) phase time)
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
        allDistinctRepresentativeSignedFluxSum
          m kappa time energy observed -
        positiveNonAllDistinctRepresentativeA1GainRemainder
          m kappa time energy observed -
        positiveInnerNonAllDistinctFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed| ≤
      ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m))‖ *
        (4 / (modeFrequency m observed ^ 2 * time)) := by
  exact abs_secondOrderBroadening_sub_resolvedTerms_le_inverseTime
    m kappa beta energy observed htime homega henergy

#print axioms
  problem_abs_secondOrderBroadening_sub_resolvedTerms_le_inverseTime

end

end ArchonPhysicsConsumers.Thermalization
