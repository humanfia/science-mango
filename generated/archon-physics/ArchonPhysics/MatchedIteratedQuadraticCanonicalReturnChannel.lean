import ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

/-!
# Canonical disjoint selector for matched iterated-quadratic return channels

The six physical return-channel predicates are complete but intentionally
overlap when modes coincide.  This module does not change those predicates
or assert that they are disjoint.  Instead it assigns each charge-matched
tree to the first predicate it satisfies in the established six-channel
order.  Equality fibers of that selector form a genuine finite partition.

The priority is

1. free observed in the `free+, inner0+, inner1-` sector;
2. inner zero observed in that sector;
3. free observed in the `free+, inner0-, inner1+` sector;
4. inner one observed in that sector;
5. inner zero observed in the `free-, inner0+, inner1+` sector;
6. inner one observed in that sector.

Thus an all-equal tree in the first, second, or third sign sector is assigned
respectively to channel one, three, or five.  No inclusion-exclusion term is
needed after passing to selector fibers.
-/

namespace ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

noncomputable section

/-- Labels in the same right-associated order as the established six-way
return-channel theorem. -/
inductive CanonicalReturnChannel
  | freeObservedInnerZeroCancelsInnerOne
  | innerZeroObservedFreeCancelsInnerOne
  | freeObservedInnerOneCancelsInnerZero
  | innerOneObservedFreeCancelsInnerZero
  | innerZeroObservedInnerOneCancelsFree
  | innerOneObservedInnerZeroCancelsFree
  deriving DecidableEq

instance : Fintype CanonicalReturnChannel where
  elems := {
    .freeObservedInnerZeroCancelsInnerOne,
    .innerZeroObservedFreeCancelsInnerOne,
    .freeObservedInnerOneCancelsInnerZero,
    .innerOneObservedFreeCancelsInnerZero,
    .innerZeroObservedInnerOneCancelsFree,
    .innerOneObservedInnerZeroCancelsFree }
  complete channel := by cases channel <;> simp

/-- The original, possibly overlapping physical predicate represented by a
channel label. -/
def CanonicalReturnChannel.RawHolds
    {N : Nat} [NeZero N] (channel : CanonicalReturnChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  match channel with
  | .freeObservedInnerZeroCancelsInnerOne =>
      FreeObservedInnerZeroCancelsInnerOne observed term
  | .innerZeroObservedFreeCancelsInnerOne =>
      InnerZeroObservedFreeCancelsInnerOne observed term
  | .freeObservedInnerOneCancelsInnerZero =>
      FreeObservedInnerOneCancelsInnerZero observed term
  | .innerOneObservedFreeCancelsInnerZero =>
      InnerOneObservedFreeCancelsInnerZero observed term
  | .innerZeroObservedInnerOneCancelsFree =>
      InnerZeroObservedInnerOneCancelsFree observed term
  | .innerOneObservedInnerZeroCancelsFree =>
      InnerOneObservedInnerZeroCancelsFree observed term

/-- Disjointized channel condition induced by the fixed first-match priority.
Unlike `RawHolds`, these six predicates are intended to be selector fibers. -/
def CanonicalReturnChannel.PriorityHolds
    {N : Nat} [NeZero N] (channel : CanonicalReturnChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  match channel with
  | .freeObservedInnerZeroCancelsInnerOne =>
      RawHolds .freeObservedInnerZeroCancelsInnerOne observed term
  | .innerZeroObservedFreeCancelsInnerOne =>
      ¬ RawHolds .freeObservedInnerZeroCancelsInnerOne observed term ∧
        RawHolds .innerZeroObservedFreeCancelsInnerOne observed term
  | .freeObservedInnerOneCancelsInnerZero =>
      ¬ RawHolds .freeObservedInnerZeroCancelsInnerOne observed term ∧
        ¬ RawHolds .innerZeroObservedFreeCancelsInnerOne observed term ∧
        RawHolds .freeObservedInnerOneCancelsInnerZero observed term
  | .innerOneObservedFreeCancelsInnerZero =>
      ¬ RawHolds .freeObservedInnerZeroCancelsInnerOne observed term ∧
        ¬ RawHolds .innerZeroObservedFreeCancelsInnerOne observed term ∧
        ¬ RawHolds .freeObservedInnerOneCancelsInnerZero observed term ∧
        RawHolds .innerOneObservedFreeCancelsInnerZero observed term
  | .innerZeroObservedInnerOneCancelsFree =>
      ¬ RawHolds .freeObservedInnerZeroCancelsInnerOne observed term ∧
        ¬ RawHolds .innerZeroObservedFreeCancelsInnerOne observed term ∧
        ¬ RawHolds .freeObservedInnerOneCancelsInnerZero observed term ∧
        ¬ RawHolds .innerOneObservedFreeCancelsInnerZero observed term ∧
        RawHolds .innerZeroObservedInnerOneCancelsFree observed term
  | .innerOneObservedInnerZeroCancelsFree =>
      ¬ RawHolds .freeObservedInnerZeroCancelsInnerOne observed term ∧
        ¬ RawHolds .innerZeroObservedFreeCancelsInnerOne observed term ∧
        ¬ RawHolds .freeObservedInnerOneCancelsInnerZero observed term ∧
        ¬ RawHolds .innerOneObservedFreeCancelsInnerZero observed term ∧
        ¬ RawHolds .innerZeroObservedInnerOneCancelsFree observed term ∧
        RawHolds .innerOneObservedInnerZeroCancelsFree observed term

/-- First-match canonical channel of a charge-matched tree.  The final branch
is sound because the matched subtype supplies the charge equality and the
six-way classification is complete. -/
def canonicalReturnChannel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    CanonicalReturnChannel := by
  classical
  exact
    if CanonicalReturnChannel.RawHolds
        .freeObservedInnerZeroCancelsInnerOne observed term.1 then
      .freeObservedInnerZeroCancelsInnerOne
    else if CanonicalReturnChannel.RawHolds
        .innerZeroObservedFreeCancelsInnerOne observed term.1 then
      .innerZeroObservedFreeCancelsInnerOne
    else if CanonicalReturnChannel.RawHolds
        .freeObservedInnerOneCancelsInnerZero observed term.1 then
      .freeObservedInnerOneCancelsInnerZero
    else if CanonicalReturnChannel.RawHolds
        .innerOneObservedFreeCancelsInnerZero observed term.1 then
      .innerOneObservedFreeCancelsInnerZero
    else if CanonicalReturnChannel.RawHolds
        .innerZeroObservedInnerOneCancelsFree observed term.1 then
      .innerZeroObservedInnerOneCancelsFree
    else
      .innerOneObservedInnerZeroCancelsFree

/-- Raw six-way completeness restated on the matched subtype. -/
theorem matchedTerm_rawSixChannels
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    CanonicalReturnChannel.RawHolds
        .freeObservedInnerZeroCancelsInnerOne observed term.1 ∨
      CanonicalReturnChannel.RawHolds
        .innerZeroObservedFreeCancelsInnerOne observed term.1 ∨
      CanonicalReturnChannel.RawHolds
        .freeObservedInnerOneCancelsInnerZero observed term.1 ∨
      CanonicalReturnChannel.RawHolds
        .innerOneObservedFreeCancelsInnerZero observed term.1 ∨
      CanonicalReturnChannel.RawHolds
        .innerZeroObservedInnerOneCancelsFree observed term.1 ∨
      CanonicalReturnChannel.RawHolds
        .innerOneObservedInnerZeroCancelsFree observed term.1 := by
  simpa only [CanonicalReturnChannel.RawHolds] using
    (matchedIteratedQuadratic_six_return_channels
      observed term.1 term.2)

/-- Every priority condition implies its underlying physical channel. -/
theorem CanonicalReturnChannel.PriorityHolds.rawHolds
    {N : Nat} [NeZero N] {channel : CanonicalReturnChannel}
    {observed : Lattice.Site N}
    {term : IteratedQuadraticSecondPicardCharacterTerm N}
    (hpriority : channel.PriorityHolds observed term) :
    channel.RawHolds observed term := by
  cases channel <;>
    simp only [CanonicalReturnChannel.PriorityHolds] at hpriority <;>
    simp only [CanonicalReturnChannel.RawHolds] <;>
    tauto

/-- Kernel-level characterization of the exact priority, including every
all-equal overlap: the selected label is `channel` exactly when its
disjointized priority condition holds. -/
theorem canonicalReturnChannel_eq_iff_priorityHolds
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (channel : CanonicalReturnChannel) :
    canonicalReturnChannel observed term = channel ↔
      channel.PriorityHolds observed term.1 := by
  classical
  have hcomplete := matchedTerm_rawSixChannels observed term
  cases channel <;>
    unfold canonicalReturnChannel
      CanonicalReturnChannel.PriorityHolds <;>
    split_ifs <;> simp_all

/-- The canonical label always satisfies the original physical channel
predicate.  This is a soundness statement, not an assertion that the six raw
predicates are disjoint. -/
theorem canonicalReturnChannel_rawHolds
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    (canonicalReturnChannel observed term).RawHolds observed term.1 := by
  apply CanonicalReturnChannel.PriorityHolds.rawHolds
  rw [← canonicalReturnChannel_eq_iff_priorityHolds]

/-- Fiber of a finite matched-tree base under the canonical selector. -/
def canonicalReturnChannelFiber
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed))
    (channel : CanonicalReturnChannel) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact base.filter fun term ↦
    canonicalReturnChannel observed term = channel

/-- Distinct selector fibers are disjoint.  No disjointness of the underlying
`RawHolds` predicates is used. -/
theorem canonicalReturnChannelFiber_disjoint
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed))
    {left right : CanonicalReturnChannel} (hne : left ≠ right) :
    Disjoint
      (canonicalReturnChannelFiber observed base left)
      (canonicalReturnChannelFiber observed base right) := by
  classical
  rw [Finset.disjoint_left]
  intro term hleft hright
  have hleftLabel := (Finset.mem_filter.mp hleft).2
  have hrightLabel := (Finset.mem_filter.mp hright).2
  exact hne (hleftLabel.symm.trans hrightLabel)

/-- Every element of the base lies in exactly its selector fiber, and every
fiber element lies in the base.  Together with pairwise disjointness this is
the required coverage statement. -/
theorem mem_base_iff_exists_mem_canonicalReturnChannelFiber
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed))
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ base ↔
      ∃ channel : CanonicalReturnChannel,
        term ∈ canonicalReturnChannelFiber observed base channel := by
  classical
  constructor
  · intro hterm
    refine ⟨canonicalReturnChannel observed term, ?_⟩
    exact Finset.mem_filter.mpr ⟨hterm, rfl⟩
  · rintro ⟨channel, hterm⟩
    exact (Finset.mem_filter.mp hterm).1

/-- Exact finite fiberwise sum for any additive commutative target. -/
theorem sum_eq_sum_canonicalReturnChannelFibers
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed))
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ base, weight term) =
      ∑ channel : CanonicalReturnChannel,
        ∑ term ∈ canonicalReturnChannelFiber observed base channel,
          weight term := by
  classical
  unfold canonicalReturnChannelFiber
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := base) (t := Finset.univ)
    (g := canonicalReturnChannel observed)
    (fun term _hterm ↦ Finset.mem_univ _) weight]

/-- Positive-inner matched terms assigned to one canonical channel. -/
def positiveInnerCanonicalReturnChannelTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (channel : CanonicalReturnChannel) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) :=
  canonicalReturnChannelFiber observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed) channel

/-- Exact six-channel partition of the compact physical positive-inner
feedback sum. -/
theorem positiveInnerCompactFeedbackSum_eq_canonicalChannelSums
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
              (iteratedQuadraticInnerMismatch m term.1) time := by
  exact sum_eq_sum_canonicalReturnChannelFibers observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed)
    (fun term ↦
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time)

/-- At positive observed frequency, the original matched feedback sum is the
same exact six-channel compact physical sum. -/
theorem matchedFeedbackBroadeningSum_eq_canonicalChannelSums
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
              (iteratedQuadraticInnerMismatch m term.1) time := by
  rw [matchedFeedbackBroadeningSum_eq_positiveInnerCompactSum
    m kappa time radius observed hObserved]
  exact positiveInnerCompactFeedbackSum_eq_canonicalChannelSums
    m kappa time radius observed

end

end ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
