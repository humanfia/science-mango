import ArchonPhysics.FreeFPUTConnectedReturnCollisionKernelBridge

/-!
# Consumer: connected return trees as collision-kernel terms

This endpoint covers the four connected return channels without asserting
that their mode relations are disjoint.  The two tadpole channels are not
absorbed into the collision kernel.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTConnectedReturnCollisionKernelBridge
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- Every connected matched return term is its branch sign times the raw
inner three-wave collision kernel and the observed/free actions. -/
theorem problem_connectedReturn_compactWeight_mul_resonance_eq_collisionKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m
      (quadraticCollisionModes
        (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term).1))
    (hchannel : MatchedIteratedQuadraticConnectedChannel observed term) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed term *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term) time =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign
              (iteratedQuadraticInnerEntry term).1) time
            (quadraticCollisionModes
              (iteratedQuadraticFirstPicardMode term)
              (iteratedQuadraticInnerEntry term).1) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (iteratedQuadraticFreeMode term)) :=
  compactWeight_mul_resonance_eq_collisionKernel_mul_actions_of_connectedChannel
    m kappa time energy observed term hEnergy hPositive hchannel

#print axioms
  problem_connectedReturn_compactWeight_mul_resonance_eq_collisionKernel

end

end ArchonPhysicsConsumers.Thermalization
