import ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition

/-!
# Intrinsic tree-level partition of the non-all-distinct FPUT feedback

The repeated-mode remainder in the exact second-order formula is indexed by
matched iterated-quadratic return trees, not by a fixed local quadratic term.
Consequently local constructor cardinalities cannot by themselves partition
that remainder: in a degenerate sector a raw tree need not have a unique
preimage under those local constructors.

This module instead reads the two relevant outer modes intrinsically from
each raw tree: its first-Picard carrier and its free outer coordinate.  Along
with the observed mode, their equality pattern has four mutually exclusive
non-all-distinct strata.  We partition an arbitrary finite matched-tree base,
specialize the result to the positive-inner base, and obtain an exact
four-term decomposition of `positiveInnerNonAllDistinctFeedbackRemainder`.

No local-image surjectivity, multiplicity formula, or collision-kernel
identification is asserted here.
-/

namespace ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

/-! ## Intrinsic recovery of the two outer modes -/

/-- Reading the selected mode from the raw outer quadratic term recovers the
first-Picard carrier of the tree. -/
@[simp] theorem returnTreeOuterQuadraticTerm_selectedMode
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (returnTreeOuterQuadraticTerm term).1
        (iteratedQuadraticFirstPicardSlot term) =
      iteratedQuadraticFirstPicardMode term := rfl

/-- Reading the opposite mode from the raw outer quadratic term recovers the
free coordinate of the tree. -/
@[simp] theorem returnTreeOuterQuadraticTerm_otherMode
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (returnTreeOuterQuadraticTerm term).1
        (otherQuadraticSlot (iteratedQuadraticFirstPicardSlot term)) =
      iteratedQuadraticFreeMode term := rfl

/-! ## Four intrinsic equality strata -/

/-- The carrier and free modes coincide away from the observed mode. -/
def ReturnCarrierFreeRepeatedAwayFromObserved
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  iteratedQuadraticFirstPicardMode term = iteratedQuadraticFreeMode term ∧
    observed ≠ iteratedQuadraticFirstPicardMode term

/-- Only the first-Picard carrier is the observed mode. -/
def ReturnObservedOnlyAtCarrier
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  observed = iteratedQuadraticFirstPicardMode term ∧
    observed ≠ iteratedQuadraticFreeMode term

/-- Only the free outer coordinate is the observed mode. -/
def ReturnObservedOnlyAtFree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  observed = iteratedQuadraticFreeMode term ∧
    observed ≠ iteratedQuadraticFirstPicardMode term

/-- The observed, carrier, and free modes all coincide. -/
def ReturnObservedAtCarrierAndFree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  observed = iteratedQuadraticFirstPicardMode term ∧
    observed = iteratedQuadraticFreeMode term

/-- At least one of the two outer return modes is observed. -/
def ReturnObservedModeDegenerate
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  observed = iteratedQuadraticFirstPicardMode term ∨
    observed = iteratedQuadraticFreeMode term

/-- Exact four-way classification of the complement of intrinsic
return-mode all-distinctness. -/
theorem not_connectedReturnTreeAllDistinct_iff_four_strata
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ¬ ConnectedReturnTreeAllDistinct observed term ↔
      ReturnCarrierFreeRepeatedAwayFromObserved observed term ∨
      ReturnObservedOnlyAtCarrier observed term ∨
      ReturnObservedOnlyAtFree observed term ∨
      ReturnObservedAtCarrierAndFree observed term := by
  unfold ConnectedReturnTreeAllDistinct
    ReturnCarrierFreeRepeatedAwayFromObserved
    ReturnObservedOnlyAtCarrier ReturnObservedOnlyAtFree
    ReturnObservedAtCarrierAndFree
  by_cases hpair : iteratedQuadraticFirstPicardMode term =
      iteratedQuadraticFreeMode term <;>
    by_cases hcarrier : observed =
      iteratedQuadraticFirstPicardMode term <;>
      by_cases hfree : observed = iteratedQuadraticFreeMode term <;>
        simp_all

/-- The three observed-mode strata are pairwise disjoint. -/
theorem returnObserved_three_strata_pairwise_disjoint
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (¬ (ReturnObservedOnlyAtCarrier observed term ∧
          ReturnObservedOnlyAtFree observed term)) ∧
      (¬ (ReturnObservedOnlyAtCarrier observed term ∧
          ReturnObservedAtCarrierAndFree observed term)) ∧
      (¬ (ReturnObservedOnlyAtFree observed term ∧
          ReturnObservedAtCarrierAndFree observed term)) := by
  unfold ReturnObservedOnlyAtCarrier ReturnObservedOnlyAtFree
    ReturnObservedAtCarrierAndFree
  aesop

/-- The repeated-away stratum is disjoint from every stratum containing an
observed outer return mode. -/
theorem returnCarrierFreeRepeatedAway_disjoint_observed
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ¬ (ReturnCarrierFreeRepeatedAwayFromObserved observed term ∧
      ReturnObservedModeDegenerate observed term) := by
  unfold ReturnCarrierFreeRepeatedAwayFromObserved
    ReturnObservedModeDegenerate
  aesop

/-! ## Finite filters on an arbitrary matched-tree base -/

def returnCarrierFreeRepeatedAwayTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed)) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact base.filter fun term ↦
    ReturnCarrierFreeRepeatedAwayFromObserved observed term.1

def returnObservedOnlyAtCarrierTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed)) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact base.filter fun term ↦ ReturnObservedOnlyAtCarrier observed term.1

def returnObservedOnlyAtFreeTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed)) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact base.filter fun term ↦ ReturnObservedOnlyAtFree observed term.1

def returnObservedAtCarrierAndFreeTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed)) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact base.filter fun term ↦
    ReturnObservedAtCarrierAndFree observed term.1

def nonAllDistinctMatchedReturnTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed)) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact base.filter fun term ↦
    ¬ ConnectedReturnTreeAllDistinct observed term.1

/-- Union of the four intrinsic strata, with classical equality hidden in
the definition so no `DecidableEq` instance leaks into theorem signatures. -/
def fourReturnModeStrataTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed)) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact returnCarrierFreeRepeatedAwayTerms observed base ∪
    returnObservedOnlyAtCarrierTerms observed base ∪
    returnObservedOnlyAtFreeTerms observed base ∪
    returnObservedAtCarrierAndFreeTerms observed base

/-- Exact finite-set partition of the non-all-distinct part of any matched
return-tree base. -/
theorem nonAllDistinctMatchedReturnTerms_eq_four_strata
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed)) :
    nonAllDistinctMatchedReturnTerms observed base =
      fourReturnModeStrataTerms observed base := by
  classical
  unfold fourReturnModeStrataTerms
  ext term
  simp only [nonAllDistinctMatchedReturnTerms,
    returnCarrierFreeRepeatedAwayTerms,
    returnObservedOnlyAtCarrierTerms, returnObservedOnlyAtFreeTerms,
    returnObservedAtCarrierAndFreeTerms, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · rintro ⟨hbase, hnot⟩
    rcases (not_connectedReturnTreeAllDistinct_iff_four_strata
      observed term.1).1 hnot with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hbase, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hbase, h⟩))
    · exact Or.inl (Or.inr ⟨hbase, h⟩)
    · exact Or.inr ⟨hbase, h⟩
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · rcases h with h | h
        · exact ⟨h.1,
            (not_connectedReturnTreeAllDistinct_iff_four_strata
              observed term.1).2 (Or.inl h.2)⟩
        · exact ⟨h.1,
            (not_connectedReturnTreeAllDistinct_iff_four_strata
              observed term.1).2 (Or.inr (Or.inl h.2))⟩
      · exact ⟨h.1,
          (not_connectedReturnTreeAllDistinct_iff_four_strata
            observed term.1).2 (Or.inr (Or.inr (Or.inl h.2)))⟩
    · exact ⟨h.1,
        (not_connectedReturnTreeAllDistinct_iff_four_strata
          observed term.1).2 (Or.inr (Or.inr (Or.inr h.2)))⟩

/-- Generic additive partition.  Each original matched tree is retained as
the index, so no constructor preimage or multiplicity is introduced. -/
theorem sum_nonAllDistinctMatchedReturnTerms_eq_four_strata
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (observed : Lattice.Site N)
    (base : Finset (FreeInitialMatchedIteratedQuadraticTerm N observed))
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ nonAllDistinctMatchedReturnTerms observed base, weight term) =
      (∑ term ∈ returnCarrierFreeRepeatedAwayTerms observed base,
          weight term) +
        (∑ term ∈ returnObservedOnlyAtCarrierTerms observed base,
          weight term) +
        (∑ term ∈ returnObservedOnlyAtFreeTerms observed base,
          weight term) +
        (∑ term ∈ returnObservedAtCarrierAndFreeTerms observed base,
          weight term) := by
  classical
  rw [nonAllDistinctMatchedReturnTerms_eq_four_strata]
  unfold fourReturnModeStrataTerms
  rw [Finset.sum_union]
  · rw [Finset.sum_union]
    · rw [Finset.sum_union]
      · rw [Finset.disjoint_left]
        intro term haway hcarrier
        have hAway := (Finset.mem_filter.mp haway).2
        have hObserved : ReturnObservedModeDegenerate observed term.1 :=
          Or.inl (Finset.mem_filter.mp hcarrier).2.1
        exact (returnCarrierFreeRepeatedAway_disjoint_observed
          observed term.1) ⟨hAway, hObserved⟩
    · rw [Finset.disjoint_left]
      intro term hleft hfree
      have hFree := (Finset.mem_filter.mp hfree).2
      rcases Finset.mem_union.mp hleft with haway | hcarrier
      · have hAway := (Finset.mem_filter.mp haway).2
        have hObserved : ReturnObservedModeDegenerate observed term.1 :=
          Or.inr hFree.1
        exact (returnCarrierFreeRepeatedAway_disjoint_observed
          observed term.1) ⟨hAway, hObserved⟩
      · have hCarrier := (Finset.mem_filter.mp hcarrier).2
        exact (returnObserved_three_strata_pairwise_disjoint
          observed term.1).1 ⟨hCarrier, hFree⟩
  · rw [Finset.disjoint_left]
    intro term hleft hboth
    have hBoth := (Finset.mem_filter.mp hboth).2
    rcases Finset.mem_union.mp hleft with hleft | hfree
    · rcases Finset.mem_union.mp hleft with haway | hcarrier
      · have hAway := (Finset.mem_filter.mp haway).2
        have hObserved : ReturnObservedModeDegenerate observed term.1 :=
          Or.inl hBoth.1
        exact (returnCarrierFreeRepeatedAway_disjoint_observed
          observed term.1) ⟨hAway, hObserved⟩
      · have hCarrier := (Finset.mem_filter.mp hcarrier).2
        exact (returnObserved_three_strata_pairwise_disjoint
          observed term.1).2.1 ⟨hCarrier, hBoth⟩
    · have hFree := (Finset.mem_filter.mp hfree).2
      exact (returnObserved_three_strata_pairwise_disjoint
        observed term.1).2.2 ⟨hFree, hBoth⟩

/-! ## Specialization to the physical positive-inner remainder -/

def positiveInnerCarrierFreeRepeatedAwayReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  returnCarrierFreeRepeatedAwayTerms observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed)

def positiveInnerObservedOnlyAtCarrierReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  returnObservedOnlyAtCarrierTerms observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed)

def positiveInnerObservedOnlyAtFreeReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  returnObservedOnlyAtFreeTerms observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed)

def positiveInnerObservedAtCarrierAndFreeReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  returnObservedAtCarrierAndFreeTerms observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed)

/-- The literal union of the four positive-inner intrinsic strata. -/
def positiveInnerFourReturnModeStrataTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  fourReturnModeStrataTerms observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed)

/-- The existing non-all-distinct base is definitionally the intrinsic
non-all-distinct filter of the positive-inner matched base. -/
theorem positiveInnerNonAllDistinctReturnTerms_eq_intrinsicFilter
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerNonAllDistinctReturnTerms m observed =
      nonAllDistinctMatchedReturnTerms observed
        (positiveInnerMatchedIteratedQuadraticTerms m observed) := by
  rfl

/-- Exact four-way set partition of the original physical remainder base. -/
theorem positiveInnerNonAllDistinctReturnTerms_eq_four_strata
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerNonAllDistinctReturnTerms m observed =
      positiveInnerFourReturnModeStrataTerms m observed := by
  rw [positiveInnerNonAllDistinctReturnTerms_eq_intrinsicFilter]
  exact nonAllDistinctMatchedReturnTerms_eq_four_strata observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed)

/-- Exact additive partition of the original physical remainder base for an
arbitrary commutative additive weight. -/
theorem sum_positiveInnerNonAllDistinctReturnTerms_eq_four_strata
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
          weight term) := by
  rw [positiveInnerNonAllDistinctReturnTerms_eq_intrinsicFilter]
  exact sum_nonAllDistinctMatchedReturnTerms_eq_four_strata observed
    (positiveInnerMatchedIteratedQuadraticTerms m observed) weight

/-- Physical feedback carried by equal carrier/free modes away from the
observed mode. -/
def positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ term ∈ positiveInnerCarrierFreeRepeatedAwayReturnTerms m observed,
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Physical feedback where only the first-Picard carrier is observed. -/
def positiveInnerObservedOnlyAtCarrierFeedbackRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ term ∈ positiveInnerObservedOnlyAtCarrierReturnTerms m observed,
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Physical feedback where only the free outer coordinate is observed. -/
def positiveInnerObservedOnlyAtFreeFeedbackRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ term ∈ positiveInnerObservedOnlyAtFreeReturnTerms m observed,
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Physical feedback where observed, carrier, and free modes all agree. -/
def positiveInnerObservedAtCarrierAndFreeFeedbackRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ term ∈ positiveInnerObservedAtCarrierAndFreeReturnTerms m observed,
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Exact physical four-stratum decomposition of the repeated-mode
positive-inner feedback remainder. -/
theorem positiveInnerNonAllDistinctFeedbackRemainder_eq_four_strata
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
          m kappa time radius observed := by
  unfold positiveInnerNonAllDistinctFeedbackRemainder
    positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder
    positiveInnerObservedOnlyAtCarrierFeedbackRemainder
    positiveInnerObservedOnlyAtFreeFeedbackRemainder
    positiveInnerObservedAtCarrierAndFreeFeedbackRemainder
  exact sum_positiveInnerNonAllDistinctReturnTerms_eq_four_strata
    m observed (fun term ↦
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time)

end

end ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
