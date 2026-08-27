import ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel

/-!
# Consumer: canonical six-channel matched return partition
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

noncomputable section

/-- The priority selector always names a physically valid raw channel. -/
theorem problem_canonicalReturnChannel_rawHolds
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    (canonicalReturnChannel observed term).RawHolds observed term.1 :=
  canonicalReturnChannel_rawHolds observed term

/-- Exact kernel-visible characterization of the all-equal priority rule. -/
theorem problem_canonicalReturnChannel_eq_iff_priorityHolds
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (channel : CanonicalReturnChannel) :
    canonicalReturnChannel observed term = channel ↔
      channel.PriorityHolds observed term.1 :=
  canonicalReturnChannel_eq_iff_priorityHolds observed term channel

/-- Any two differently labelled fibers of an arbitrary matched-tree base
are disjoint. -/
theorem problem_canonicalReturnChannelFiber_disjoint
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed))
    {left right : CanonicalReturnChannel} (hne : left ≠ right) :
    Disjoint
      (canonicalReturnChannelFiber observed base left)
      (canonicalReturnChannelFiber observed base right) :=
  canonicalReturnChannelFiber_disjoint observed base hne

/-- The six selector fibers cover an arbitrary matched-tree base. -/
theorem problem_mem_base_iff_exists_mem_canonicalReturnChannelFiber
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed))
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ base ↔
      ∃ channel : CanonicalReturnChannel,
        term ∈ canonicalReturnChannelFiber observed base channel :=
  mem_base_iff_exists_mem_canonicalReturnChannelFiber observed base term

/-- Generic exact additive decomposition along the six selector fibers. -/
theorem problem_sum_eq_sum_canonicalReturnChannelFibers
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed))
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ base, weight term) =
      ∑ channel : CanonicalReturnChannel,
        ∑ term ∈ canonicalReturnChannelFiber observed base channel,
          weight term :=
  sum_eq_sum_canonicalReturnChannelFibers observed base weight

/-- Physical compact-feedback specialization on the positive-inner base. -/
theorem problem_positiveInnerCompactFeedbackSum_eq_canonicalChannelSums
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed,
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) =
      ∑ channel : CanonicalReturnChannel,
        ∑ term ∈ positiveInnerCanonicalReturnChannelTerms
            m observed channel,
          compactIteratedQuadraticStaticFeedbackWeight
              m kappa radius observed term.1 *
            finiteTimeResonanceWeight
              (iteratedQuadraticInnerMismatch m term.1) time :=
  positiveInnerCompactFeedbackSum_eq_canonicalChannelSums
    m kappa time radius observed

/-- Original matched feedback rewritten as the exact canonical six-channel
physical sum at positive observed frequency. -/
theorem problem_matchedFeedbackBroadeningSum_eq_canonicalChannelSums
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    (∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
      iteratedQuadraticFeedbackStaticWeight m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) =
      ∑ channel : CanonicalReturnChannel,
        ∑ term ∈ positiveInnerCanonicalReturnChannelTerms
            m observed channel,
          compactIteratedQuadraticStaticFeedbackWeight
              m kappa radius observed term.1 *
            finiteTimeResonanceWeight
              (iteratedQuadraticInnerMismatch m term.1) time :=
  matchedFeedbackBroadeningSum_eq_canonicalChannelSums
    m kappa time radius observed hObserved

#print axioms problem_canonicalReturnChannel_rawHolds
#print axioms problem_canonicalReturnChannel_eq_iff_priorityHolds
#print axioms problem_canonicalReturnChannelFiber_disjoint
#print axioms problem_mem_base_iff_exists_mem_canonicalReturnChannelFiber
#print axioms problem_sum_eq_sum_canonicalReturnChannelFibers
#print axioms problem_positiveInnerCompactFeedbackSum_eq_canonicalChannelSums
#print axioms problem_matchedFeedbackBroadeningSum_eq_canonicalChannelSums

end

end ArchonPhysicsConsumers.Thermalization
