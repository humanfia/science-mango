import ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity

/-!
# Consumer: global all-equal selector and multiplicity

This gate exposes the restricted tadpole involution, the exact surviving
channel-five fiber, its canonical multiplicity, and the resulting signed
all-equal A1-plus-feedback formula.  No cancellation over a non-invariant
subset is assumed.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- The restricted selector fiber is genuinely closed under the tadpole
involution. -/
theorem problem_allEqualOuter_selectorFiber_flip_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (channel : CanonicalReturnChannel)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    flipMatchedIteratedQuadraticInnerBranch observed term ∈
        positiveInnerAllEqualOuterCanonicalTerms m observed channel ↔
      term ∈ positiveInnerAllEqualOuterCanonicalTerms
        m observed channel :=
  mem_positiveInnerAllEqualOuterCanonicalTerms_flip_iff
    m observed channel term

/-- Restricted tadpoles cancel and the original all-equal outer remainder
is exactly selector channel five. -/
theorem problem_allEqualOuter_feedback_eq_channelFive
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveInnerObservedAtCarrierAndFreeFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      ∑ term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
          .innerZeroObservedInnerOneCancelsFree,
        allEqualPhysicalFeedbackWeight
          m kappa time energy observed term :=
  positiveInnerObservedAtCarrierAndFreeFeedbackRemainder_eq_channelFive
    m kappa time energy observed

/-- The surviving literal tree fiber and the canonical collapsed parameter
base have exactly the same cardinality. -/
theorem problem_card_allEqualOuter_channelFive_eq_parameters
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    (positiveInnerAllEqualOuterCanonicalTerms m observed
      .innerZeroObservedInnerOneCancelsFree).card =
      (positiveAllEqualChannelFiveParameters N m observed).card :=
  card_positiveInnerAllEqualOuterChannelFive_eq_parameters m observed

/-- Exact all-equal A1 gain plus signed channel-five correction with its
proved global multiplicity. -/
theorem problem_allEqualA1Gain_add_feedback_eq_signedParameters
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveObservedAtBothChildrenRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerObservedAtCarrierAndFreeFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      (∑ q ∈ positiveObservedAtBothChildrenRepresentatives N m observed,
        ((FreeFPUTQuadraticTermSwapSymmetry.quadraticSwapOrbit q).card :
            Real) ^ 2 *
          MicroscopicFiniteTimeCollisionPolynomial.finiteTimeCollisionKernel
            m kappa
            (FreeFPUTCollisionMismatchBridge.quadraticCollisionSign q) time
            (FreeFPUTCollisionMismatchBridge.quadraticCollisionModes
              observed q) *
          FreeFPUTEnergyCollisionWeightBridge.modeAction energy
            (modeFrequency m) observed ^ 2) +
      ∑ parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
        (FreeFPUTCollisionMismatchBridge.quadraticInputInteractionSign
          parameter.1 parameter.2.1).coefficient *
          MicroscopicFiniteTimeCollisionPolynomial.finiteTimeCollisionKernel
            m kappa
            (FreeFPUTCollisionMismatchBridge.quadraticCollisionSign
              parameter.1) time
            (FreeFPUTCollisionMismatchBridge.quadraticCollisionModes
              observed parameter.1) *
          FreeFPUTEnergyCollisionWeightBridge.modeAction energy
            (modeFrequency m) observed ^ 2 :=
  allEqualRepresentativeA1Gain_add_feedback_eq_signedParameters
    m kappa time energy observed hEnergy

#print axioms problem_allEqualOuter_selectorFiber_flip_iff
#print axioms problem_allEqualOuter_feedback_eq_channelFive
#print axioms problem_card_allEqualOuter_channelFive_eq_parameters
#print axioms problem_allEqualA1Gain_add_feedback_eq_signedParameters

end

end ArchonPhysicsConsumers.Thermalization
