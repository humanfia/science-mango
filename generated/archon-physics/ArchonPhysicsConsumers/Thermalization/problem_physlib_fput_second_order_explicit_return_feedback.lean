import ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

/-!
# Consumer: explicit physical return feedback at second order
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteVolumeGainFeedbackDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

theorem problem_normalized_secondOrder_eq_gain_cross_explicitFeedback
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
      (∑ representative ∈
          positiveQuadraticSwapOrbitRepresentatives N m observed,
        ((quadraticSwapOrbit representative).card : Real) ^ 2 *
          (finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign representative) time
              (quadraticCollisionModes observed representative) *
            ∏ r : Fin 2,
              modeAction energy (modeFrequency m)
                (representative.1 r))) +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re +
        ∑ term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed,
          compactIteratedQuadraticStaticFeedbackWeight m kappa
              (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
            finiteTimeResonanceWeight
              (iteratedQuadraticInnerMismatch m term.1) time :=
  normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_gain_cross_explicitFeedback
    m kappa beta energy observed htime homega henergy

#print axioms problem_normalized_secondOrder_eq_gain_cross_explicitFeedback

end

end ArchonPhysicsConsumers.Thermalization
