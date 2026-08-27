import ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber

/-!
# Consumer: canonical connected fibers on the all-distinct sector

These statements expose the exact reduction of the six canonical return
channels to the four connected labels.  The reduction is made only under
pairwise mode distinctness; no disjointness of the raw predicates is claimed
on repeated-mode strata.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-- An all-distinct matched return tree is necessarily in a raw connected
channel. -/
theorem problem_connectedChannel_of_allDistinct_matched
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1) :
    MatchedIteratedQuadraticConnectedChannel observed term.1 :=
  connectedChannel_of_allDistinct_matched observed term hDistinct

/-- The six-way canonical selector lands in exactly the four connected
labels on this sector. -/
theorem problem_canonicalReturnChannel_mem_connected_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1) :
    canonicalReturnChannel observed term ∈
      canonicalConnectedReturnChannels :=
  canonicalReturnChannel_mem_connected_of_allDistinct
    observed term hDistinct

/-- Direct bridge to the original positive-inner canonical fibers. -/
theorem problem_mem_allDistinctConnected_iff_originalFibers
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed ↔
      ConnectedReturnTreeAllDistinct observed term.1 ∧
        ∃ channel ∈ canonicalConnectedReturnChannels,
          term ∈ positiveInnerCanonicalReturnChannelTerms
            m observed channel :=
  mem_positiveInnerAllDistinctConnectedReturnTerms_iff_originalFibers
    m observed term

/-- Exact finite weighted sum over the four disjoint selector fibers. -/
theorem problem_sum_allDistinctConnected_eq_fourFibers
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed,
        weight term) =
      ∑ channel ∈ canonicalConnectedReturnChannels,
        ∑ term ∈ positiveInnerAllDistinctCanonicalReturnChannelTerms
            m observed channel,
          weight term :=
  sum_positiveInnerAllDistinctConnectedReturnTerms_eq_fourFibers
    m observed weight

#print axioms problem_connectedChannel_of_allDistinct_matched
#print axioms problem_canonicalReturnChannel_mem_connected_of_allDistinct
#print axioms problem_mem_allDistinctConnected_iff_originalFibers
#print axioms problem_sum_allDistinctConnected_eq_fourFibers

end

end ArchonPhysicsConsumers.Thermalization
