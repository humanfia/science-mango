import ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctGainPartition

/-!
# Consumer gate: exact second-order all-distinct gain partition
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
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

theorem problem_normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_allDistinctGain_add_remainders
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
      allDistinctRepresentativeA1GainSum
          m kappa time energy observed +
        positiveNonAllDistinctRepresentativeA1GainRemainder
          m kappa time energy observed +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re +
        ∑ term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed,
          compactIteratedQuadraticStaticFeedbackWeight m kappa
              (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
            finiteTimeResonanceWeight
              (iteratedQuadraticInnerMismatch m term.1) time :=
  normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_allDistinctGain_add_remainders
    m kappa beta energy observed htime homega henergy

#print axioms
  problem_normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_allDistinctGain_add_remainders

end

end ArchonPhysicsConsumers.Thermalization
