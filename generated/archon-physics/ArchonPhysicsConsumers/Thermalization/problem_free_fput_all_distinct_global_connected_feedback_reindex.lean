import ArchonPhysics.FreeFPUTAllDistinctGlobalConnectedFeedbackReindex

/-!
# Consumer gate: global all-distinct connected-feedback reindex

These theorems expose the exact identification of the original
positive-inner all-distinct feedback with the representative-indexed local
eight-tree sum.  They deliberately do not identify the full feedback with
this sector: repeated-mode boundary strata remain separate corrections.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber
open ArchonPhysics.FreeFPUTAllDistinctGlobalConnectedFeedbackReindex
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- The physical weighted sum on the original positive-inner all-distinct
matched return-tree base is exactly the representative-indexed connected
feedback sum. -/
theorem problem_sum_positiveInnerAllDistinctConnectedFeedback_eq_representative
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    (∑ term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed,
      compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) =
      allDistinctRepresentativeConnectedFeedbackSum
        m kappa time energy observed :=
  sum_positiveInnerAllDistinctConnectedFeedback_eq_representative
    m kappa time energy observed hObserved

/-- Equivalent four-selector-fiber form of the global reindex.  Each fiber
is explicitly restricted to all-distinct terms. -/
theorem problem_sum_fourAllDistinctCanonicalConnectedFibers_feedback_eq_representative
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    (∑ channel ∈ canonicalConnectedReturnChannels,
      ∑ term ∈ positiveInnerAllDistinctCanonicalReturnChannelTerms
          m observed channel,
        compactIteratedQuadraticStaticFeedbackWeight m kappa
            (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time) =
      allDistinctRepresentativeConnectedFeedbackSum
        m kappa time energy observed :=
  sum_fourAllDistinctCanonicalConnectedFibers_feedback_eq_representative
    m kappa time energy observed hObserved

#print axioms
  problem_sum_positiveInnerAllDistinctConnectedFeedback_eq_representative
#print axioms
  problem_sum_fourAllDistinctCanonicalConnectedFibers_feedback_eq_representative

end

end ArchonPhysicsConsumers.Thermalization
