import ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation

/-!
# Consumer: exact cancellation of canonical tadpole feedback

The two tadpole sectors are summed on the disjoint first-match selector
fibers.  In particular, all-equal raw overlap with a connected predicate is
owned by the earlier canonical fiber and is not counted twice.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- Consumer-facing form of exact cancellation in canonical tadpole channel
one. -/
theorem problem_canonicalTadpoleChannelOne_feedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerCanonicalReturnChannelTerms m observed
        .freeObservedInnerZeroCancelsInnerOne,
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) = 0 :=
  canonicalTadpoleChannelOne_compactFeedbackSum_eq_zero
    m kappa time radius observed

/-- Consumer-facing form of exact cancellation in canonical tadpole channel
three. -/
theorem problem_canonicalTadpoleChannelThree_feedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerCanonicalReturnChannelTerms m observed
        .freeObservedInnerOneCancelsInnerZero,
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) = 0 :=
  canonicalTadpoleChannelThree_compactFeedbackSum_eq_zero
    m kappa time radius observed

/-- The two disjoint canonical tadpole fibers make no net contribution to
the compact finite-time feedback sum. -/
theorem problem_canonicalTadpoleFibers_feedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerCanonicalReturnChannelTerms m observed
        .freeObservedInnerZeroCancelsInnerOne,
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) +
      (∑ term ∈ positiveInnerCanonicalReturnChannelTerms m observed
          .freeObservedInnerOneCancelsInnerZero,
        compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time) = 0 :=
  canonicalTadpoleFibers_compactFeedbackSum_eq_zero
    m kappa time radius observed

#print axioms problem_canonicalTadpoleChannelOne_feedbackSum_eq_zero
#print axioms problem_canonicalTadpoleChannelThree_feedbackSum_eq_zero
#print axioms problem_canonicalTadpoleFibers_feedbackSum_eq_zero

end

end ArchonPhysicsConsumers.Thermalization
