import ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
import ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation

/-!
# Observed-child boundary strata of the finite FPUT collision sum

The complement of the pairwise all-distinct collision sector has four
elementary mode-equality strata.  This module isolates the three strata in
which the observed mode is one or both quadratic inputs, while retaining the
fourth (equal children away from the observed mode) as a disjoint comparison
stratum.  The resulting filters give an exact finite partition of any
quadratic base, and in particular of the positive canonical swap-orbit
representatives.

There is an additional first-match issue on an observed-child stratum.  When
the free leg of a constructed return tree is also the observed mode, all
three return modes coincide.  If that free leg has binary sign zero, the two
inner placements belong respectively to canonical tadpole channels one and
three.  If it has binary sign one, the placements are literally identical
and the unique tree belongs to canonical connected channel five.  Thus the
all-equal overlap is assigned exactly once; the channel-one/three terms are
already covered by the global tadpole involution and must not be counted a
second time as connected feedback.
-/

namespace ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- The observed mode is exactly input zero, but not input one. -/
def ObservedOnlyAtChildZero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Prop :=
  observed = q.1 0 ∧ observed ≠ q.1 1

/-- The observed mode is exactly input one, but not input zero. -/
def ObservedOnlyAtChildOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Prop :=
  observed = q.1 1 ∧ observed ≠ q.1 0

/-- The observed mode and both quadratic input modes coincide. -/
def ObservedAtBothChildren
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Prop :=
  observed = q.1 0 ∧ observed = q.1 1

/-- The two children coincide at a mode separated from the observed mode. -/
def RepeatedChildrenAwayFromObserved
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Prop :=
  q.1 0 = q.1 1 ∧ observed ≠ q.1 0

/-- The observed-child part of the degenerate sector. -/
def ObservedChildDegenerate
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Prop :=
  observed = q.1 0 ∨ observed = q.1 1

/-- Exact three-way classification of observed-child coincidence. -/
theorem observedChildDegenerate_iff_three_strata
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    ObservedChildDegenerate observed q ↔
      ObservedOnlyAtChildZero observed q ∨
      ObservedOnlyAtChildOne observed q ∨
      ObservedAtBothChildren observed q := by
  unfold ObservedChildDegenerate ObservedOnlyAtChildZero
    ObservedOnlyAtChildOne ObservedAtBothChildren
  by_cases hzero : observed = q.1 0 <;>
    by_cases hone : observed = q.1 1 <;> simp_all

/-- Exact four-way classification of the complement of pairwise
all-distinctness. -/
theorem not_observedQuadraticAllDistinct_iff_four_strata
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    ¬ ObservedQuadraticAllDistinct observed q ↔
      RepeatedChildrenAwayFromObserved observed q ∨
      ObservedOnlyAtChildZero observed q ∨
      ObservedOnlyAtChildOne observed q ∨
      ObservedAtBothChildren observed q := by
  unfold ObservedQuadraticAllDistinct RepeatedChildrenAwayFromObserved
    ObservedOnlyAtChildZero ObservedOnlyAtChildOne ObservedAtBothChildren
  by_cases hchildren : q.1 0 = q.1 1 <;>
    by_cases hzero : observed = q.1 0 <;>
      by_cases hone : observed = q.1 1 <;> simp_all

/-- The three observed-child strata are pairwise disjoint. -/
theorem observedChild_three_strata_pairwise_disjoint
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    (¬ (ObservedOnlyAtChildZero observed q ∧
          ObservedOnlyAtChildOne observed q)) ∧
      (¬ (ObservedOnlyAtChildZero observed q ∧
          ObservedAtBothChildren observed q)) ∧
      (¬ (ObservedOnlyAtChildOne observed q ∧
          ObservedAtBothChildren observed q)) := by
  unfold ObservedOnlyAtChildZero ObservedOnlyAtChildOne
    ObservedAtBothChildren
  aesop

/-- The equal-children-away stratum is disjoint from every observed-child
stratum. -/
theorem repeatedChildrenAway_disjoint_observedChild
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    ¬ (RepeatedChildrenAwayFromObserved observed q ∧
      ObservedChildDegenerate observed q) := by
  unfold RepeatedChildrenAwayFromObserved ObservedChildDegenerate
  aesop

/-- Generic finite filter for the observed-at-child-zero-only stratum. -/
def observedOnlyAtChildZeroTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (QuadraticPhaseTerm N)) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact base.filter (ObservedOnlyAtChildZero observed)

/-- Generic finite filter for the observed-at-child-one-only stratum. -/
def observedOnlyAtChildOneTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (QuadraticPhaseTerm N)) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact base.filter (ObservedOnlyAtChildOne observed)

/-- Generic finite filter for the all-three-modes-equal stratum. -/
def observedAtBothChildrenTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (QuadraticPhaseTerm N)) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact base.filter (ObservedAtBothChildren observed)

/-- Generic finite filter for equal children away from the observed mode. -/
def repeatedChildrenAwayFromObservedTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (QuadraticPhaseTerm N)) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact base.filter (RepeatedChildrenAwayFromObserved observed)

/-- Generic finite filter for the entire non-all-distinct sector. -/
def nonAllDistinctQuadraticTerms
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (QuadraticPhaseTerm N)) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact base.filter fun q ↦ ¬ ObservedQuadraticAllDistinct observed q

/-- Exact finite-set partition of the non-all-distinct portion of any
quadratic base. -/
theorem filter_not_allDistinct_eq_four_strata
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (base : Finset (QuadraticPhaseTerm N)) :
    nonAllDistinctQuadraticTerms observed base =
      repeatedChildrenAwayFromObservedTerms observed base ∪
        observedOnlyAtChildZeroTerms observed base ∪
        observedOnlyAtChildOneTerms observed base ∪
        observedAtBothChildrenTerms observed base := by
  classical
  ext q
  simp only [nonAllDistinctQuadraticTerms, Finset.mem_filter, Finset.mem_union,
    repeatedChildrenAwayFromObservedTerms,
    observedOnlyAtChildZeroTerms, observedOnlyAtChildOneTerms,
    observedAtBothChildrenTerms]
  constructor
  · rintro ⟨hbase, hnot⟩
    rcases (not_observedQuadraticAllDistinct_iff_four_strata
      observed q).1 hnot with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hbase, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hbase, h⟩))
    · exact Or.inl (Or.inr ⟨hbase, h⟩)
    · exact Or.inr ⟨hbase, h⟩
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · rcases h with h | h
        · exact ⟨h.1,
            (not_observedQuadraticAllDistinct_iff_four_strata
              observed q).2 (Or.inl h.2)⟩
        · exact ⟨h.1,
            (not_observedQuadraticAllDistinct_iff_four_strata
              observed q).2 (Or.inr (Or.inl h.2))⟩
      · exact ⟨h.1,
          (not_observedQuadraticAllDistinct_iff_four_strata
            observed q).2 (Or.inr (Or.inr (Or.inl h.2)))⟩
    · exact ⟨h.1,
        (not_observedQuadraticAllDistinct_iff_four_strata
          observed q).2 (Or.inr (Or.inr (Or.inr h.2)))⟩

/-- Exact additive four-stratum identity, with no inclusion-exclusion
correction because the predicates are mutually exclusive. -/
theorem sum_filter_not_allDistinct_eq_four_strata
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (observed : Lattice.Site N) (base : Finset (QuadraticPhaseTerm N))
    (weight : QuadraticPhaseTerm N → M) :
    (∑ q ∈ nonAllDistinctQuadraticTerms observed base, weight q) =
      (∑ q ∈ repeatedChildrenAwayFromObservedTerms observed base,
          weight q) +
        (∑ q ∈ observedOnlyAtChildZeroTerms observed base, weight q) +
        (∑ q ∈ observedOnlyAtChildOneTerms observed base, weight q) +
        (∑ q ∈ observedAtBothChildrenTerms observed base, weight q) := by
  classical
  rw [filter_not_allDistinct_eq_four_strata]
  rw [Finset.sum_union]
  · rw [Finset.sum_union]
    · rw [Finset.sum_union]
      · rw [Finset.disjoint_left]
        intro q haway hzero
        have hAway := (Finset.mem_filter.mp haway).2
        have hObserved : ObservedChildDegenerate observed q :=
          Or.inl (Finset.mem_filter.mp hzero).2.1
        exact (repeatedChildrenAway_disjoint_observedChild observed q)
          ⟨hAway, hObserved⟩
    · rw [Finset.disjoint_left]
      intro q hleft hone
      have hOne := (Finset.mem_filter.mp hone).2
      rcases Finset.mem_union.mp hleft with haway | hzero
      · have hAway := (Finset.mem_filter.mp haway).2
        have hObserved : ObservedChildDegenerate observed q := Or.inr hOne.1
        exact (repeatedChildrenAway_disjoint_observedChild observed q)
          ⟨hAway, hObserved⟩
      · have hZero := (Finset.mem_filter.mp hzero).2
        exact (observedChild_three_strata_pairwise_disjoint observed q).1
          ⟨hZero, hOne⟩
  · rw [Finset.disjoint_left]
    intro q hleft hboth
    have hBoth := (Finset.mem_filter.mp hboth).2
    rcases Finset.mem_union.mp hleft with hleft | hone
    · rcases Finset.mem_union.mp hleft with haway | hzero
      · have hAway := (Finset.mem_filter.mp haway).2
        have hObserved : ObservedChildDegenerate observed q := Or.inl hBoth.1
        exact (repeatedChildrenAway_disjoint_observedChild observed q)
          ⟨hAway, hObserved⟩
      · have hZero := (Finset.mem_filter.mp hzero).2
        exact (observedChild_three_strata_pairwise_disjoint observed q).2.1
          ⟨hZero, hBoth⟩
    · have hOne := (Finset.mem_filter.mp hone).2
      exact (observedChild_three_strata_pairwise_disjoint observed q).2.2
        ⟨hOne, hBoth⟩

/-- On a constructed tree whose free mode is observed, binary free sign zero
and inner observed placement zero force first-match channel one. -/
theorem canonicalReturnChannel_connectedReturnTree_allEqual_freeSignZero_innerZero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r))
    (hsign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 0) :
    canonicalReturnChannel observed
        (matchedConnectedReturnTree observed q r outerSlot 0) =
      .freeObservedInnerZeroCancelsInnerOne := by
  rw [canonicalReturnChannel_eq_iff_priorityHolds]
  unfold CanonicalReturnChannel.PriorityHolds
    CanonicalReturnChannel.RawHolds
    FreeObservedInnerZeroCancelsInnerOne
  simp only [matchedConnectedReturnTree]
  rw [connectedReturnTree_freeSignedLeg,
    connectedReturnTree_adjustedInnerLeg_selected,
    show (1 : Fin 2) = otherQuadraticSlot 0 by rfl,
    connectedReturnTree_adjustedInnerLeg_other]
  simp [hmode, hsign, binarySignedMode, binaryPhaseSign,
    positiveSignedMode]

/-- The other inner placement in the same free-positive all-equal overlap is
assigned to first-match channel three, not to a connected channel. -/
theorem canonicalReturnChannel_connectedReturnTree_allEqual_freeSignZero_innerOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r))
    (hsign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 0) :
    canonicalReturnChannel observed
        (matchedConnectedReturnTree observed q r outerSlot 1) =
      .freeObservedInnerOneCancelsInnerZero := by
  rw [canonicalReturnChannel_eq_iff_priorityHolds]
  unfold CanonicalReturnChannel.PriorityHolds
    CanonicalReturnChannel.RawHolds
    FreeObservedInnerZeroCancelsInnerOne
    InnerZeroObservedFreeCancelsInnerOne
    FreeObservedInnerOneCancelsInnerZero
  simp only [matchedConnectedReturnTree]
  rw [connectedReturnTree_freeSignedLeg,
    connectedReturnTree_adjustedInnerLeg_selected,
    show (0 : Fin 2) = otherQuadraticSlot 1 by rfl,
    connectedReturnTree_adjustedInnerLeg_other]
  simp [hmode, hsign, binarySignedMode, binaryPhaseSign,
    positiveSignedMode]

/-- With binary free sign one, both adjusted inner legs are positive at the
observed mode, so first-match chooses connected channel five. -/
theorem canonicalReturnChannel_connectedReturnTree_allEqual_freeSignOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r))
    (hsign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 1) :
    canonicalReturnChannel observed
      (matchedConnectedReturnTree observed q r outerSlot innerSlot) =
      .innerZeroObservedInnerOneCancelsFree := by
  have hfree := connectedReturnTree_freeSignedLeg
    observed q r outerSlot innerSlot
  have hinnerZero :
      adjustedFirstPicardInnerLeg
          (iteratedQuadraticInnerEntry
            (connectedReturnTree observed q r outerSlot innerSlot)) 0 =
        positiveSignedMode observed := by
    by_cases hzero : innerSlot = 0
    · subst innerSlot
      exact connectedReturnTree_adjustedInnerLeg_selected
        observed q r outerSlot 0
    · have hone : innerSlot = 1 := Fin.eq_one_of_ne_zero innerSlot hzero
      subst innerSlot
      have hother := connectedReturnTree_adjustedInnerLeg_other
        observed q r outerSlot 1
      simpa [hmode, hsign, binarySignedMode, binaryPhaseSign,
        positiveSignedMode] using hother
  have hinnerOne :
      adjustedFirstPicardInnerLeg
          (iteratedQuadraticInnerEntry
            (connectedReturnTree observed q r outerSlot innerSlot)) 1 =
        positiveSignedMode observed := by
    by_cases hone : innerSlot = 1
    · subst innerSlot
      exact connectedReturnTree_adjustedInnerLeg_selected
        observed q r outerSlot 1
    · have hzero : innerSlot = 0 := by
        fin_cases innerSlot <;> simp_all
      subst innerSlot
      have hother := connectedReturnTree_adjustedInnerLeg_other
        observed q r outerSlot 0
      simpa [hmode, hsign, binarySignedMode, binaryPhaseSign,
        positiveSignedMode] using hother
  rw [canonicalReturnChannel_eq_iff_priorityHolds]
  unfold CanonicalReturnChannel.PriorityHolds
    CanonicalReturnChannel.RawHolds
    FreeObservedInnerZeroCancelsInnerOne
    InnerZeroObservedFreeCancelsInnerOne
    FreeObservedInnerOneCancelsInnerZero
    InnerOneObservedFreeCancelsInnerZero
    InnerZeroObservedInnerOneCancelsFree
  simp only [matchedConnectedReturnTree]
  rw [hfree, hinnerZero, hinnerOne]
  simp [hmode, hsign, binarySignedMode, binaryPhaseSign,
    positiveSignedMode]

/-- The two placement choices for a fixed distinguished input. -/
abbrev FixedDistinguishedReturnPlacement := Fin 2 × Fin 2

/-- Matched connected-return constructor with the distinguished input held
fixed and only the outer/inner placements varying. -/
def fixedDistinguishedReturnMap
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (placement : FixedDistinguishedReturnPlacement) :
    FreeInitialMatchedIteratedQuadraticTerm N observed :=
  matchedConnectedReturnTree observed q r placement.1 placement.2

/-- Literal finite image of the four nominal placements. -/
def fixedDistinguishedReturnImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact Finset.univ.image (fixedDistinguishedReturnMap observed q r)

/-- Binary free sign zero distinguishes the two inner placements even if
their modes coincide: the adjusted signs are positive and conjugate. -/
theorem fixedDistinguishedReturnMap_injective_of_freeSignZero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hsign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 0) :
    Function.Injective (fixedDistinguishedReturnMap observed q r) := by
  rintro ⟨outerLeft, innerLeft⟩ ⟨outerRight, innerRight⟩ htree
  have hraw := congrArg Subtype.val htree
  change connectedReturnTree observed q r outerLeft innerLeft =
    connectedReturnTree observed q r outerRight innerRight at hraw
  have houter : outerLeft = outerRight := by
    simpa using
      congrArg iteratedQuadraticFirstPicardSlot hraw
  subst outerRight
  rcases q with ⟨modes, signZero, signOne⟩
  fin_cases r <;> fin_cases innerLeft <;> fin_cases innerRight <;>
    fin_cases signZero <;> fin_cases signOne <;>
    simp_all [connectedReturnTree, connectedReturnInnerTerm,
      connectedReturnInnerModes, connectedReturnRawInnerSign,
      connectedReturnAdjustedInnerSign, connectedReturnOuterModes,
      twoSlotPlacement, quadraticPhaseTermBinarySign,
      coordinateBranchAdjustedBinarySign]

/-- Therefore the fixed-input image has all four nominal trees in the
free-positive sign sector, including the all-equal tadpole overlap. -/
theorem card_fixedDistinguishedReturnImage_eq_four_of_freeSignZero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hsign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 0) :
    (fixedDistinguishedReturnImage observed q r).card = 4 := by
  classical
  unfold fixedDistinguishedReturnImage
  rw [Finset.card_image_of_injective _
    (fixedDistinguishedReturnMap_injective_of_freeSignZero
      observed q r hsign)]
  decide

/-- Mode separation is the other mechanism that keeps all four placements
distinct, independently of the free binary sign. -/
theorem fixedDistinguishedReturnMap_injective_of_observed_ne_other
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hmode : observed ≠ q.1 (otherQuadraticSlot r)) :
    Function.Injective (fixedDistinguishedReturnMap observed q r) := by
  intro left right htree
  apply connectedReturnTree_placement_injective observed q r hmode
  exact congrArg Subtype.val htree

/-- A mode-separated fixed-input image has cardinality four. -/
theorem card_fixedDistinguishedReturnImage_eq_four_of_observed_ne_other
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hmode : observed ≠ q.1 (otherQuadraticSlot r)) :
    (fixedDistinguishedReturnImage observed q r).card = 4 := by
  classical
  unfold fixedDistinguishedReturnImage
  rw [Finset.card_image_of_injective _
    (fixedDistinguishedReturnMap_injective_of_observed_ne_other
      observed q r hmode)]
  decide

/-- In the free-negative all-equal sector both adjusted inner legs are the
same positive signed mode, so changing the inner placement does not change
the raw return tree. -/
theorem connectedReturnTree_innerPlacement_eq_zero_of_allEqual_freeSignOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r))
    (hsign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 1) :
    connectedReturnTree observed q r outerSlot innerSlot =
      connectedReturnTree observed q r outerSlot 0 := by
  have hmodes : connectedReturnInnerModes observed q r innerSlot =
      connectedReturnInnerModes observed q r 0 := by
    funext input
    fin_cases innerSlot <;> fin_cases input <;>
      simp [connectedReturnInnerModes, twoSlotPlacement, hmode]
  have hadjusted : connectedReturnAdjustedInnerSign q r innerSlot =
      connectedReturnAdjustedInnerSign q r 0 := by
    funext input
    fin_cases innerSlot <;> fin_cases input <;>
      simp [connectedReturnAdjustedInnerSign, twoSlotPlacement, hsign]
  have hinner : connectedReturnInnerTerm observed q r innerSlot =
      connectedReturnInnerTerm observed q r 0 := by
    unfold connectedReturnInnerTerm
    rw [hmodes]
    congr 1
    apply Prod.ext
    · unfold connectedReturnRawInnerSign
      rw [congrFun hadjusted 0]
    · unfold connectedReturnRawInnerSign
      rw [congrFun hadjusted 1]
  unfold connectedReturnTree
  rw [hinner]

/-- The two-element outer-placement constructor after the redundant inner
placement has been removed. -/
def collapsedAllEqualReturnMap
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot : Fin 2) :
    FreeInitialMatchedIteratedQuadraticTerm N observed :=
  matchedConnectedReturnTree observed q r outerSlot 0

/-- Literal two-element image in the collapsed sector. -/
def collapsedAllEqualReturnImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact Finset.univ.image (collapsedAllEqualReturnMap observed q r)

/-- The stored first-Picard slot makes the two outer placements distinct. -/
theorem collapsedAllEqualReturnMap_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2) :
    Function.Injective (collapsedAllEqualReturnMap observed q r) := by
  intro left right htree
  have hraw := congrArg Subtype.val htree
  change connectedReturnTree observed q r left 0 =
    connectedReturnTree observed q r right 0 at hraw
  simpa using
    congrArg iteratedQuadraticFirstPicardSlot hraw

/-- Exact finite-image equality behind the `4 → 2` multiplicity collapse. -/
theorem fixedDistinguishedReturnImage_eq_collapsed_of_allEqual_freeSignOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r))
    (hsign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 1) :
    fixedDistinguishedReturnImage observed q r =
      collapsedAllEqualReturnImage observed q r := by
  classical
  ext term
  simp only [fixedDistinguishedReturnImage,
    collapsedAllEqualReturnImage, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨outerSlot, innerSlot⟩, rfl⟩
    refine ⟨outerSlot, ?_⟩
    apply Subtype.ext
    exact (connectedReturnTree_innerPlacement_eq_zero_of_allEqual_freeSignOne
      observed q r outerSlot innerSlot hmode hsign).symm
  · rintro ⟨outerSlot, rfl⟩
    exact ⟨(outerSlot, 0), rfl⟩

/-- Hence the free-negative all-equal fixed-input image contains exactly two
trees, both owned by canonical channel five. -/
theorem card_fixedDistinguishedReturnImage_eq_two_of_allEqual_freeSignOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r))
    (hsign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 1) :
    (fixedDistinguishedReturnImage observed q r).card = 2 := by
  classical
  rw [fixedDistinguishedReturnImage_eq_collapsed_of_allEqual_freeSignOne
    observed q r hmode hsign]
  unfold collapsedAllEqualReturnImage
  rw [Finset.card_image_of_injective _
    (collapsedAllEqualReturnMap_injective observed q r)]
  decide

/-- Complete first-match formula on the all-equal return overlap.  The
free-positive sector is split between the two already-cancelling tadpole
fibers; the free-negative sector is owned by connected channel five. -/
theorem canonicalReturnChannel_connectedReturnTree_allEqual_piecewise
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
        .innerZeroObservedInnerOneCancelsFree := by
  by_cases hsignZero : quadraticPhaseTermBinarySign q
      (otherQuadraticSlot r) = 0
  · rw [if_pos hsignZero]
    by_cases hinnerZero : innerSlot = 0
    · subst innerSlot
      rw [if_pos rfl]
      exact
        canonicalReturnChannel_connectedReturnTree_allEqual_freeSignZero_innerZero
          observed q r outerSlot hmode hsignZero
    · have hinnerOne : innerSlot = 1 :=
        Fin.eq_one_of_ne_zero innerSlot hinnerZero
      subst innerSlot
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      exact
        canonicalReturnChannel_connectedReturnTree_allEqual_freeSignZero_innerOne
          observed q r outerSlot hmode hsignZero
  · rw [if_neg hsignZero]
    have hsignOne : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 1 :=
      Fin.eq_one_of_ne_zero _ hsignZero
    exact canonicalReturnChannel_connectedReturnTree_allEqual_freeSignOne
      observed q r outerSlot innerSlot hmode hsignOne

/-- Exact piecewise multiplicity of a fixed-distinguished-input return
image at the observed-child boundary.  This is the finite correction
`4 → 2` caused by identifying the two inner placements in channel five. -/
theorem card_fixedDistinguishedReturnImage_allEqual_piecewise
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hmode : observed = q.1 (otherQuadraticSlot r)) :
    (fixedDistinguishedReturnImage observed q r).card =
      if quadraticPhaseTermBinarySign q (otherQuadraticSlot r) = 0 then
        4
      else
        2 := by
  by_cases hsignZero : quadraticPhaseTermBinarySign q
      (otherQuadraticSlot r) = 0
  · rw [if_pos hsignZero]
    exact card_fixedDistinguishedReturnImage_eq_four_of_freeSignZero
      observed q r hsignZero
  · rw [if_neg hsignZero]
    have hsignOne : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot r) = 1 :=
      Fin.eq_one_of_ne_zero _ hsignZero
    exact card_fixedDistinguishedReturnImage_eq_two_of_allEqual_freeSignOne
      observed q r hmode hsignOne

/-- The full literal local image when `selected` is the unique quadratic
input carrying the observed mode.  The first half distinguishes that input;
the second half distinguishes the other input and therefore has an
all-equal return overlap. -/
def observedExactlyOneChildReturnImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact fixedDistinguishedReturnImage observed q selected ∪
    fixedDistinguishedReturnImage observed q
      (otherQuadraticSlot selected)

/-- The two fixed-distinguished-input halves are disjoint whenever the
observed child is separated from the other child. -/
theorem fixedDistinguishedReturnImages_disjoint_of_observed_exactly_one
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hObserved : observed = q.1 selected)
    (hSeparated : observed ≠ q.1 (otherQuadraticSlot selected)) :
    Disjoint
      (fixedDistinguishedReturnImage observed q selected)
      (fixedDistinguishedReturnImage observed q
        (otherQuadraticSlot selected)) := by
  classical
  rw [Finset.disjoint_left]
  intro term hleft hright
  rcases Finset.mem_image.mp hleft with ⟨left, _hleftUniv, hleftEq⟩
  rcases Finset.mem_image.mp hright with ⟨right, _hrightUniv, hrightEq⟩
  have htree : fixedDistinguishedReturnMap observed q selected left =
      fixedDistinguishedReturnMap observed q
        (otherQuadraticSlot selected) right :=
    hleftEq.trans hrightEq.symm
  have hmodes := congrArg iteratedQuadraticFirstPicardMode
    (congrArg Subtype.val htree)
  have hbad : q.1 selected = q.1 (otherQuadraticSlot selected) := by
    simpa [fixedDistinguishedReturnMap, matchedConnectedReturnTree] using hmodes
  exact hSeparated (hObserved.trans hbad)

/-- Exact local multiplicity for an observed-equals-exactly-one-child
stratum: eight distinct trees when the observed child has binary sign zero,
and six when it has binary sign one.  The missing two are precisely the
collapsed inner placements of canonical channel five. -/
theorem card_observedExactlyOneChildReturnImage_piecewise
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hObserved : observed = q.1 selected)
    (hSeparated : observed ≠ q.1 (otherQuadraticSlot selected)) :
    (observedExactlyOneChildReturnImage observed q selected).card =
      if quadraticPhaseTermBinarySign q selected = 0 then 8 else 6 := by
  classical
  unfold observedExactlyOneChildReturnImage
  rw [Finset.card_union_of_disjoint
    (fixedDistinguishedReturnImages_disjoint_of_observed_exactly_one
      observed q selected hObserved hSeparated)]
  rw [card_fixedDistinguishedReturnImage_eq_four_of_observed_ne_other
    observed q selected hSeparated]
  have hmodeOther : observed =
      q.1 (otherQuadraticSlot (otherQuadraticSlot selected)) := by
    simpa using hObserved
  rw [card_fixedDistinguishedReturnImage_allEqual_piecewise
    observed q (otherQuadraticSlot selected) hmodeOther]
  simp only [FreeFPUTCanonicalConnectedReturnTree.otherQuadraticSlot_involutive]
  by_cases hsign : quadraticPhaseTermBinarySign q selected = 0
  · rw [if_pos hsign, if_pos hsign]
  · rw [if_neg hsign, if_neg hsign]

end

end ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
