import ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
import ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

/-!
# Consumer: observed-child boundary partition and multiplicity

This consumer exposes the exact finite decomposition of the positive
canonical quadratic base at the non-all-distinct boundary.  It also records
the first-match ownership and literal image multiplicity of the all-equal
return overlap.  Canonical tadpole channels one and three are already
annihilated by the global branch-flip involution; channel five is retained as
a connected contribution with two, rather than four, distinct trees.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- Consumer-facing exact logical classification of every mode-degenerate
quadratic collision triple. -/
theorem problem_nonAllDistinct_iff_four_boundary_strata
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    ¬ ObservedQuadraticAllDistinct observed q ↔
      RepeatedChildrenAwayFromObserved observed q ∨
      ObservedOnlyAtChildZero observed q ∨
      ObservedOnlyAtChildOne observed q ∨
      ObservedAtBothChildren observed q :=
  not_observedQuadraticAllDistinct_iff_four_strata observed q

/-- Exact additive partition instantiated on the physically relevant
positive-frequency canonical swap-orbit representatives. -/
theorem problem_positiveCanonical_nonAllDistinct_sum_eq_four_strata
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (weight : QuadraticPhaseTerm N → M) :
    (∑ q ∈ nonAllDistinctQuadraticTerms observed
        (positiveQuadraticSwapOrbitRepresentatives N m observed), weight q) =
      (∑ q ∈ repeatedChildrenAwayFromObservedTerms observed
          (positiveQuadraticSwapOrbitRepresentatives N m observed),
          weight q) +
        (∑ q ∈ observedOnlyAtChildZeroTerms observed
            (positiveQuadraticSwapOrbitRepresentatives N m observed),
            weight q) +
        (∑ q ∈ observedOnlyAtChildOneTerms observed
            (positiveQuadraticSwapOrbitRepresentatives N m observed),
            weight q) +
        (∑ q ∈ observedAtBothChildrenTerms observed
            (positiveQuadraticSwapOrbitRepresentatives N m observed),
            weight q) :=
  sum_filter_not_allDistinct_eq_four_strata observed
    (positiveQuadraticSwapOrbitRepresentatives N m observed) weight

/-- First-match ownership of every all-equal return constructor.  In
particular, no raw tadpole/connected overlap is counted twice. -/
theorem problem_allEqualReturn_firstMatch_piecewise
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r)) :
    canonicalReturnChannel observed
        (matchedConnectedReturnTree observed q r outerSlot innerSlot) =
      if quadraticPhaseTermBinarySign q (otherQuadraticSlot r) = 0 then
        if innerSlot = 0 then
          .freeObservedInnerZeroCancelsInnerOne
        else
          .freeObservedInnerOneCancelsInnerZero
      else
        .innerZeroObservedInnerOneCancelsFree :=
  canonicalReturnChannel_connectedReturnTree_allEqual_piecewise
    observed q r outerSlot innerSlot hmode

/-- Exact finite multiplicity correction on the same overlap: four literal
trees in the free-positive tadpole sector, two in the free-negative
connected sector. -/
theorem problem_allEqualReturn_fixedInput_card_piecewise
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r)) :
    (fixedDistinguishedReturnImage observed q r).card =
      if quadraticPhaseTermBinarySign q (otherQuadraticSlot r) = 0 then
        4
      else
        2 :=
  card_fixedDistinguishedReturnImage_allEqual_piecewise
    observed q r hmode

/-- For a quadratic representative with exactly one observed child, the
complete two-distinguished-input local image has cardinality eight or six.
The `8 → 6` correction is exactly the twofold collapse in channel five. -/
theorem problem_observedExactlyOneChild_fullLocalImage_card_piecewise
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hObserved : observed = q.1 selected)
    (hSeparated : observed ≠ q.1 (otherQuadraticSlot selected)) :
    (observedExactlyOneChildReturnImage observed q selected).card =
      if quadraticPhaseTermBinarySign q selected = 0 then 8 else 6 :=
  card_observedExactlyOneChildReturnImage_piecewise
    observed q selected hObserved hSeparated

/-- The channel-one/channel-three terms singled out above have zero total
compact feedback on the full positive-inner canonical base. -/
theorem problem_allEqualTadpoleOwnership_already_cancels
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

#print axioms problem_nonAllDistinct_iff_four_boundary_strata
#print axioms problem_positiveCanonical_nonAllDistinct_sum_eq_four_strata
#print axioms problem_allEqualReturn_firstMatch_piecewise
#print axioms problem_allEqualReturn_fixedInput_card_piecewise
#print axioms problem_observedExactlyOneChild_fullLocalImage_card_piecewise
#print axioms problem_allEqualTadpoleOwnership_already_cancels

end

end ArchonPhysicsConsumers.Thermalization
