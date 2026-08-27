import ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition

/-!
# Consumer: intrinsic tree-level repeated-mode feedback partition

This gate exposes the exact four-way partition on the original matched-tree
base.  It deliberately makes no claim that a degenerate tree has a unique
preimage under a fixed-quadratic-term local constructor.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- Every non-all-distinct raw return tree has exactly one of the four
intrinsic observed/carrier/free equality patterns. -/
theorem problem_nonAllDistinctReturnTree_iff_four_strata
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ¬ ConnectedReturnTreeAllDistinct observed term ↔
      ReturnCarrierFreeRepeatedAwayFromObserved observed term ∨
      ReturnObservedOnlyAtCarrier observed term ∨
      ReturnObservedOnlyAtFree observed term ∨
      ReturnObservedAtCarrierAndFree observed term :=
  not_connectedReturnTreeAllDistinct_iff_four_strata observed term

/-- Generic sum partition on the exact original positive-inner
non-all-distinct matched-tree base. -/
theorem problem_sum_positiveInnerNonAllDistinctReturnTerms_eq_four_strata
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ positiveInnerNonAllDistinctReturnTerms m observed,
        weight term) =
      (∑ term ∈ positiveInnerCarrierFreeRepeatedAwayReturnTerms m observed,
          weight term) +
        (∑ term ∈ positiveInnerObservedOnlyAtCarrierReturnTerms m observed,
          weight term) +
        (∑ term ∈ positiveInnerObservedOnlyAtFreeReturnTerms m observed,
          weight term) +
        (∑ term ∈ positiveInnerObservedAtCarrierAndFreeReturnTerms m observed,
          weight term) :=
  sum_positiveInnerNonAllDistinctReturnTerms_eq_four_strata
    m observed weight

/-- Physical specialization: the exact repeated-mode feedback remainder is
the sum of its four intrinsic tree-level equality strata. -/
theorem problem_positiveInnerNonAllDistinctFeedbackRemainder_eq_four_strata
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveInnerNonAllDistinctFeedbackRemainder
        m kappa time radius observed =
      positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder
          m kappa time radius observed +
        positiveInnerObservedOnlyAtCarrierFeedbackRemainder
          m kappa time radius observed +
        positiveInnerObservedOnlyAtFreeFeedbackRemainder
          m kappa time radius observed +
        positiveInnerObservedAtCarrierAndFreeFeedbackRemainder
          m kappa time radius observed :=
  positiveInnerNonAllDistinctFeedbackRemainder_eq_four_strata
    m kappa time radius observed

#print axioms problem_nonAllDistinctReturnTree_iff_four_strata
#print axioms problem_sum_positiveInnerNonAllDistinctReturnTerms_eq_four_strata
#print axioms
  problem_positiveInnerNonAllDistinctFeedbackRemainder_eq_four_strata

end

end ArchonPhysicsConsumers.Thermalization
