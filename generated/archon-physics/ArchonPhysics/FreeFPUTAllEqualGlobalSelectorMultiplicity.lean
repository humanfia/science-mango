import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
import ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
import ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
import ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
import ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation

/-!
# Global selector and multiplicity on the all-equal FPUT boundary

The intrinsic tree stratum in which the first-Picard carrier and the free
outer mode both equal the observed mode is larger than the local all-equal
collision image: its two adjusted inner legs may cancel at an arbitrary
mode.  The first-match selector separates this excess exactly.  Channels one
and three are tadpole fibers, and their intersections with the intrinsic
all-equal outer stratum are closed under the inner-branch involution.  They
therefore cancel without applying a full-fiber cancellation theorem to an
unproved local subset.  The surviving channel-five fiber has all three modes
equal and is the genuine local all-equal collision feedback.

This file first proves that selector statement and the restricted tadpole
cancellations.  It then records the exact canonical parameters for the
surviving channel-five fiber, including the `4 -> 2` inner-placement collapse.
-/

namespace ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-! ## First-match restriction on the intrinsic all-equal outer stratum -/

/-- Restrict the intrinsic all-equal outer tree stratum to one canonical
first-match selector fiber. -/
def positiveInnerAllEqualOuterCanonicalTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (channel : CanonicalReturnChannel) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) :=
  canonicalReturnChannelFiber observed
    (positiveInnerObservedAtCarrierAndFreeReturnTerms m observed) channel

/-- On the all-equal outer stratum, raw channel two already satisfies the
earlier raw channel-one predicate. -/
theorem rawChannelOne_of_allEqualOuter_rawChannelTwo
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hAll : ReturnObservedAtCarrierAndFree observed term)
    (hTwo : InnerZeroObservedFreeCancelsInnerOne observed term) :
    FreeObservedInnerZeroCancelsInnerOne observed term := by
  unfold ReturnObservedAtCarrierAndFree at hAll
  unfold InnerZeroObservedFreeCancelsInnerOne at hTwo
  unfold FreeObservedInnerZeroCancelsInnerOne
  dsimp only at hTwo ⊢
  rcases hTwo with ⟨hfree, hzero, hone, hzeroMode, hcancel⟩
  refine ⟨hfree, hzero, hone, ?_, ?_⟩
  · simpa [iteratedQuadraticFreeSignedLeg, binarySignedMode] using
      hAll.2.symm
  · exact hzeroMode.trans (hAll.2.trans hcancel)

/-- On the all-equal outer stratum, raw channel four already satisfies the
earlier raw channel-three predicate. -/
theorem rawChannelThree_of_allEqualOuter_rawChannelFour
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hAll : ReturnObservedAtCarrierAndFree observed term)
    (hFour : InnerOneObservedFreeCancelsInnerZero observed term) :
    FreeObservedInnerOneCancelsInnerZero observed term := by
  unfold ReturnObservedAtCarrierAndFree at hAll
  unfold InnerOneObservedFreeCancelsInnerZero at hFour
  unfold FreeObservedInnerOneCancelsInnerZero
  dsimp only at hFour ⊢
  rcases hFour with ⟨hfree, hzero, hone, honeMode, hcancel⟩
  refine ⟨hfree, hzero, hone, ?_, ?_⟩
  · simpa [iteratedQuadraticFreeSignedLeg, binarySignedMode] using
      hAll.2.symm
  · exact honeMode.trans (hAll.2.trans hcancel)

/-- On the all-equal outer stratum, raw channel six already satisfies the
earlier raw channel-five predicate. -/
theorem rawChannelFive_of_allEqualOuter_rawChannelSix
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hAll : ReturnObservedAtCarrierAndFree observed term)
    (hSix : InnerOneObservedInnerZeroCancelsFree observed term) :
    InnerZeroObservedInnerOneCancelsFree observed term := by
  unfold ReturnObservedAtCarrierAndFree at hAll
  unfold InnerOneObservedInnerZeroCancelsFree at hSix
  unfold InnerZeroObservedInnerOneCancelsFree
  dsimp only at hSix ⊢
  rcases hSix with ⟨hfree, hzero, hone, honeMode, hcancel⟩
  have hfreeMode :
      (iteratedQuadraticFreeSignedLeg term).mode = observed := by
    simpa [iteratedQuadraticFreeSignedLeg, binarySignedMode] using
      hAll.2.symm
  refine ⟨hfree, hzero, hone, ?_, ?_⟩
  · exact hcancel.trans hfreeMode
  · exact honeMode.trans hfreeMode.symm

/-- First-match can select only channels one, three, or five on the
intrinsic all-equal outer stratum. -/
theorem canonicalReturnChannel_mem_one_three_five_of_allEqualOuter
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hAll : ReturnObservedAtCarrierAndFree observed term.1) :
    canonicalReturnChannel observed term =
        .freeObservedInnerZeroCancelsInnerOne ∨
      canonicalReturnChannel observed term =
        .freeObservedInnerOneCancelsInnerZero ∨
      canonicalReturnChannel observed term =
        .innerZeroObservedInnerOneCancelsFree := by
  generalize hChannel : canonicalReturnChannel observed term = channel
  have hPriority : channel.PriorityHolds observed term.1 :=
    (canonicalReturnChannel_eq_iff_priorityHolds
      observed term channel).1 hChannel
  change channel = _ ∨ channel = _ ∨ channel = _
  cases channel with
  | freeObservedInnerZeroCancelsInnerOne => exact Or.inl rfl
  | innerZeroObservedFreeCancelsInnerOne =>
      simp only [CanonicalReturnChannel.PriorityHolds] at hPriority
      exact (hPriority.1
        (rawChannelOne_of_allEqualOuter_rawChannelTwo
          observed term.1 hAll hPriority.2)).elim
  | freeObservedInnerOneCancelsInnerZero => exact Or.inr (Or.inl rfl)
  | innerOneObservedFreeCancelsInnerZero =>
      simp only [CanonicalReturnChannel.PriorityHolds] at hPriority
      exact (hPriority.2.2.1
        (rawChannelThree_of_allEqualOuter_rawChannelFour
          observed term.1 hAll hPriority.2.2.2)).elim
  | innerZeroObservedInnerOneCancelsFree => exact Or.inr (Or.inr rfl)
  | innerOneObservedInnerZeroCancelsFree =>
      simp only [CanonicalReturnChannel.PriorityHolds] at hPriority
      exact (hPriority.2.2.2.2.1
        (rawChannelFive_of_allEqualOuter_rawChannelSix
          observed term.1 hAll hPriority.2.2.2.2.2)).elim

/-- The all-equal outer restriction of channel two is empty. -/
theorem positiveInnerAllEqualOuter_channelTwo_eq_empty
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerAllEqualOuterCanonicalTerms m observed
        .innerZeroObservedFreeCancelsInnerOne = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro term hTerm
  have hFiltered := Finset.mem_filter.mp hTerm
  have hBase := hFiltered.1
  have hLabel := hFiltered.2
  have hAll := (Finset.mem_filter.mp hBase).2
  rcases canonicalReturnChannel_mem_one_three_five_of_allEqualOuter
      observed term hAll with h | h | h <;> simp_all

/-- The all-equal outer restriction of channel four is empty. -/
theorem positiveInnerAllEqualOuter_channelFour_eq_empty
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerAllEqualOuterCanonicalTerms m observed
        .innerOneObservedFreeCancelsInnerZero = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro term hTerm
  have hFiltered := Finset.mem_filter.mp hTerm
  have hBase := hFiltered.1
  have hLabel := hFiltered.2
  have hAll := (Finset.mem_filter.mp hBase).2
  rcases canonicalReturnChannel_mem_one_three_five_of_allEqualOuter
      observed term hAll with h | h | h <;> simp_all

/-- The all-equal outer restriction of channel six is empty. -/
theorem positiveInnerAllEqualOuter_channelSix_eq_empty
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerAllEqualOuterCanonicalTerms m observed
        .innerOneObservedInnerZeroCancelsFree = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro term hTerm
  have hFiltered := Finset.mem_filter.mp hTerm
  have hBase := hFiltered.1
  have hLabel := hFiltered.2
  have hAll := (Finset.mem_filter.mp hBase).2
  rcases canonicalReturnChannel_mem_one_three_five_of_allEqualOuter
      observed term hAll with h | h | h <;> simp_all

/-- Literal union of the three possible first-match fibers on the intrinsic
all-equal outer base.  Classical equality is hidden here so that no
`DecidableEq` argument leaks into theorem signatures. -/
def positiveInnerAllEqualOuterThreeFibers
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact
    (positiveInnerAllEqualOuterCanonicalTerms m observed
        .freeObservedInnerZeroCancelsInnerOne ∪
      positiveInnerAllEqualOuterCanonicalTerms m observed
        .freeObservedInnerOneCancelsInnerZero) ∪
    positiveInnerAllEqualOuterCanonicalTerms m observed
      .innerZeroObservedInnerOneCancelsFree

/-- Exact three-fiber selector partition of the intrinsic all-equal outer
base. -/
theorem positiveInnerObservedAtCarrierAndFreeReturnTerms_eq_threeFibers
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerObservedAtCarrierAndFreeReturnTerms m observed =
      positiveInnerAllEqualOuterThreeFibers m observed := by
  classical
  unfold positiveInnerAllEqualOuterThreeFibers
  ext term
  simp only [Finset.mem_union]
  constructor
  · intro hBase
    have hAll := (Finset.mem_filter.mp hBase).2
    rcases canonicalReturnChannel_mem_one_three_five_of_allEqualOuter
        observed term hAll with h | h | h
    · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hBase, h⟩))
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hBase, h⟩))
    · exact Or.inr (Finset.mem_filter.mpr ⟨hBase, h⟩)
  · rintro ((h | h) | h) <;>
      exact (Finset.mem_filter.mp h).1

/-! ## Restricted tadpole involutions -/

/-- The intrinsic all-equal outer restriction of every selector fiber is
closed under the inner-branch flip. -/
@[simp] theorem mem_positiveInnerAllEqualOuterCanonicalTerms_flip_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (channel : CanonicalReturnChannel)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    flipMatchedIteratedQuadraticInnerBranch observed term ∈
        positiveInnerAllEqualOuterCanonicalTerms m observed channel ↔
      term ∈ positiveInnerAllEqualOuterCanonicalTerms
        m observed channel := by
  classical
  unfold positiveInnerAllEqualOuterCanonicalTerms
    canonicalReturnChannelFiber
    positiveInnerObservedAtCarrierAndFreeReturnTerms
    returnObservedAtCarrierAndFreeTerms
    ReturnObservedAtCarrierAndFree
  simp only [Finset.mem_filter,
    mem_positiveInnerMatchedIteratedQuadraticTerms_flip_iff,
    canonicalReturnChannel_flipMatchedIteratedQuadraticInnerBranch,
    flipMatchedIteratedQuadraticInnerBranch_coe,
    flipIteratedQuadraticInnerBranch_firstPicardMode,
    flipIteratedQuadraticInnerBranch_freeMode]

/-- The compact physical feedback summand used throughout this module. -/
def allEqualPhysicalFeedbackWeight
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) : Real :=
  compactIteratedQuadraticStaticFeedbackWeight m kappa
      (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
    finiteTimeResonanceWeight
      (iteratedQuadraticInnerMismatch m term.1) time

/-- Channel-one cancellation remains valid after restricting to the
all-equal outer subset, because that subset has now been proved invariant. -/
theorem allEqualOuter_channelOne_feedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
        .freeObservedInnerZeroCancelsInnerOne,
      allEqualPhysicalFeedbackWeight
        m kappa time energy observed term) = 0 := by
  classical
  apply Finset.sum_involution
    (fun term _hterm ↦
      flipMatchedIteratedQuadraticInnerBranch observed term)
  · intro term hterm
    change allEqualPhysicalFeedbackWeight
          m kappa time energy observed term +
        allEqualPhysicalFeedbackWeight m kappa time energy observed
          (flipMatchedIteratedQuadraticInnerBranch observed term) = 0
    unfold allEqualPhysicalFeedbackWeight
    have hFull : term ∈ positiveInnerCanonicalReturnChannelTerms
        m observed .freeObservedInnerZeroCancelsInnerOne := by
      unfold positiveInnerAllEqualOuterCanonicalTerms
        canonicalReturnChannelFiber at hterm
      unfold positiveInnerCanonicalReturnChannelTerms
        canonicalReturnChannelFiber
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hterm).1).1,
          (Finset.mem_filter.mp hterm).2⟩
    simp only [flipMatchedIteratedQuadraticInnerBranch_coe]
    rw [compactFeedbackSummand_flip_eq_neg_of_tadpole
      m kappa time (phaseEnergyRadius energy (modeFrequency m))
      observed term.1
      (tadpole_of_mem_positiveInnerCanonicalChannelOne
        m observed term hFull)]
    ring
  · intro term _hterm _hnonzero
    exact flipMatchedIteratedQuadraticInnerBranch_ne observed term
  · intro term hterm
    exact (mem_positiveInnerAllEqualOuterCanonicalTerms_flip_iff
      m observed .freeObservedInnerZeroCancelsInnerOne term).2 hterm
  · intro term _hterm
    exact flipMatchedIteratedQuadraticInnerBranch_involutive observed term

/-- Channel-three cancellation likewise survives the all-equal outer
restriction. -/
theorem allEqualOuter_channelThree_feedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
        .freeObservedInnerOneCancelsInnerZero,
      allEqualPhysicalFeedbackWeight
        m kappa time energy observed term) = 0 := by
  classical
  apply Finset.sum_involution
    (fun term _hterm ↦
      flipMatchedIteratedQuadraticInnerBranch observed term)
  · intro term hterm
    change allEqualPhysicalFeedbackWeight
          m kappa time energy observed term +
        allEqualPhysicalFeedbackWeight m kappa time energy observed
          (flipMatchedIteratedQuadraticInnerBranch observed term) = 0
    unfold allEqualPhysicalFeedbackWeight
    have hFull : term ∈ positiveInnerCanonicalReturnChannelTerms
        m observed .freeObservedInnerOneCancelsInnerZero := by
      unfold positiveInnerAllEqualOuterCanonicalTerms
        canonicalReturnChannelFiber at hterm
      unfold positiveInnerCanonicalReturnChannelTerms
        canonicalReturnChannelFiber
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hterm).1).1,
          (Finset.mem_filter.mp hterm).2⟩
    simp only [flipMatchedIteratedQuadraticInnerBranch_coe]
    rw [compactFeedbackSummand_flip_eq_neg_of_tadpole
      m kappa time (phaseEnergyRadius energy (modeFrequency m))
      observed term.1
      (tadpole_of_mem_positiveInnerCanonicalChannelThree
        m observed term hFull)]
    ring
  · intro term _hterm _hnonzero
    exact flipMatchedIteratedQuadraticInnerBranch_ne observed term
  · intro term hterm
    exact (mem_positiveInnerAllEqualOuterCanonicalTerms_flip_iff
      m observed .freeObservedInnerOneCancelsInnerZero term).2 hterm
  · intro term _hterm
    exact flipMatchedIteratedQuadraticInnerBranch_involutive observed term

/-- After the two restricted tadpole cancellations, the complete intrinsic
all-equal outer feedback is exactly its channel-five selector fiber. -/
theorem positiveInnerObservedAtCarrierAndFreeFeedbackRemainder_eq_channelFive
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveInnerObservedAtCarrierAndFreeFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      ∑ term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
          .innerZeroObservedInnerOneCancelsFree,
        allEqualPhysicalFeedbackWeight
          m kappa time energy observed term := by
  classical
  unfold positiveInnerObservedAtCarrierAndFreeFeedbackRemainder
  rw [positiveInnerObservedAtCarrierAndFreeReturnTerms_eq_threeFibers]
  unfold positiveInnerAllEqualOuterThreeFibers
  rw [Finset.sum_union]
  · rw [Finset.sum_union]
    · change
        (∑ term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
            .freeObservedInnerZeroCancelsInnerOne,
          allEqualPhysicalFeedbackWeight
            m kappa time energy observed term) +
          (∑ term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
            .freeObservedInnerOneCancelsInnerZero,
          allEqualPhysicalFeedbackWeight
            m kappa time energy observed term) +
          (∑ term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
            .innerZeroObservedInnerOneCancelsFree,
          allEqualPhysicalFeedbackWeight
            m kappa time energy observed term) = _
      rw [allEqualOuter_channelOne_feedbackSum_eq_zero,
        allEqualOuter_channelThree_feedbackSum_eq_zero]
      ring
    · simpa [positiveInnerAllEqualOuterCanonicalTerms] using
        (canonicalReturnChannelFiber_disjoint observed
          (positiveInnerObservedAtCarrierAndFreeReturnTerms m observed)
          (show CanonicalReturnChannel.freeObservedInnerZeroCancelsInnerOne ≠
            .freeObservedInnerOneCancelsInnerZero by decide))
  · rw [Finset.disjoint_left]
    intro term hLeft hFive
    have hFiveLabel := (Finset.mem_filter.mp hFive).2
    rcases Finset.mem_union.mp hLeft with hOne | hThree
    · have hOneLabel := (Finset.mem_filter.mp hOne).2
      exact (show
        CanonicalReturnChannel.freeObservedInnerZeroCancelsInnerOne ≠
          .innerZeroObservedInnerOneCancelsFree by decide)
        (hOneLabel.symm.trans hFiveLabel)
    · have hThreeLabel := (Finset.mem_filter.mp hThree).2
      exact (show
        CanonicalReturnChannel.freeObservedInnerOneCancelsInnerZero ≠
          .innerZeroObservedInnerOneCancelsFree by decide)
        (hThreeLabel.symm.trans hFiveLabel)

/-! ## Canonical parameters for the surviving channel-five fiber -/

/-- On a swap-fixed all-equal quadratic term, only distinguished slot zero
is retained.  On a genuine two-element swap orbit both slots are retained.
This is the global removal of the `(q,r) ~ (swap q, other r)` redundancy. -/
def canonicalAllEqualDistinguishedSlots
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) : Finset (Fin 2) := by
  classical
  exact if swapQuadraticPhaseTerm q = q then {0} else Finset.univ

/-- A retained distinguished slot whose opposite (free) character is the
negative/conjugate character.  Exactly these parameters land in selector
channel five. -/
def canonicalAllEqualChannelFiveSlots
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) : Finset (Fin 2) := by
  classical
  exact (canonicalAllEqualDistinguishedSlots q).filter fun r ↦
    quadraticPhaseTermBinarySign q (otherQuadraticSlot r) = 1

/-- For every binary sign pair there is at most one canonical
channel-five distinguished slot. -/
theorem canonicalAllEqualChannelFiveSlots_unique
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    {left right : Fin 2}
    (hModes : q.1 0 = q.1 1)
    (hLeft : left ∈ canonicalAllEqualChannelFiveSlots q)
    (hRight : right ∈ canonicalAllEqualChannelFiveSlots q) :
    left = right := by
  rcases q with ⟨modes, signZero, signOne⟩
  have hModesFun : modes ∘ ⇑(Equiv.swap (0 : Fin 2) 1) = modes := by
    funext input
    fin_cases input
    · simpa using hModes.symm
    · simpa using hModes
  fin_cases signZero <;> fin_cases signOne <;>
    fin_cases left <;> fin_cases right <;>
    simp_all [canonicalAllEqualChannelFiveSlots,
      canonicalAllEqualDistinguishedSlots, swapQuadraticPhaseTerm,
      quadraticInputSlotSwap, quadraticPhaseTermBinarySign,
      otherQuadraticSlot]

/-- Global finite parameter base: a positive canonical all-equal quadratic
representative, its unique channel-five distinguished slot when it exists,
and one of the two surviving outer placements. -/
def positiveAllEqualChannelFiveParameters
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (QuadraticPhaseTerm N × (Fin 2 × Fin 2)) := by
  classical
  exact (positiveObservedAtBothChildrenRepresentatives N m observed).biUnion
    fun q ↦ (canonicalAllEqualChannelFiveSlots q).biUnion fun r ↦
      Finset.univ.image fun outerSlot ↦ (q, (r, outerSlot))

/-- The literal collapsed constructor attached to a canonical parameter. -/
def positiveAllEqualChannelFiveReturnMap
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2)) :
    FreeInitialMatchedIteratedQuadraticTerm N observed :=
  matchedConnectedReturnTree observed parameter.1 parameter.2.1
    parameter.2.2 0

/-- Membership exposes exactly the three components of the parameter
filter. -/
theorem mem_positiveAllEqualChannelFiveParameters_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2)) :
    parameter ∈ positiveAllEqualChannelFiveParameters N m observed ↔
      parameter.1 ∈
          positiveObservedAtBothChildrenRepresentatives N m observed ∧
        parameter.2.1 ∈
          canonicalAllEqualChannelFiveSlots parameter.1 := by
  classical
  simp only [positiveAllEqualChannelFiveParameters, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, r, hr, outerSlot, hParameter⟩
    subst parameter
    exact ⟨hq, hr⟩
  · rintro ⟨hq, hr⟩
    exact ⟨parameter.1, hq, parameter.2.1, hr,
      parameter.2.2, rfl⟩

/-- Membership in the all-equal positive representative base. -/
theorem mem_positiveObservedAtBothChildrenRepresentatives_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    q ∈ positiveObservedAtBothChildrenRepresentatives N m observed ↔
      q ∈ quadraticSwapOrbitRepresentatives N ∧
        PositiveModeTuple m (quadraticCollisionModes observed q) ∧
        ObservedAtBothChildren observed q := by
  classical
  simp only [positiveObservedAtBothChildrenRepresentatives,
    observedAtBothChildrenTerms, positiveQuadraticSwapOrbitRepresentatives,
    Finset.mem_filter]
  tauto

/-- Every canonical parameter maps into the surviving selector-five fiber. -/
theorem positiveAllEqualChannelFiveReturnMap_mem_channelFive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2))
    (hParameter : parameter ∈
      positiveAllEqualChannelFiveParameters N m observed) :
    positiveAllEqualChannelFiveReturnMap observed parameter ∈
      positiveInnerAllEqualOuterCanonicalTerms m observed
        .innerZeroObservedInnerOneCancelsFree := by
  classical
  rcases parameter with ⟨q, ⟨r, outerSlot⟩⟩
  have hParts :=
    (mem_positiveAllEqualChannelFiveParameters_iff
      m observed (q, (r, outerSlot))).1 hParameter
  have hqParts :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed q).1 hParts.1
  have hslot := Finset.mem_filter.mp hParts.2
  have hAll := hqParts.2.2
  have hmode : observed = q.1 (otherQuadraticSlot r) := by
    fin_cases r
    · exact hAll.2
    · exact hAll.1
  have hcarrierMode : observed = q.1 r := by
    fin_cases r
    · exact hAll.1
    · exact hAll.2
  have hCarrier : 0 < modeFrequency m (q.1 r) := by
    simpa [quadraticCollisionModes] using
      hqParts.2.1 (Fin.succ r)
  unfold positiveInnerAllEqualOuterCanonicalTerms
    canonicalReturnChannelFiber
    positiveInnerObservedAtCarrierAndFreeReturnTerms
    returnObservedAtCarrierAndFreeTerms
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · unfold positiveInnerMatchedIteratedQuadraticTerms
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [positiveAllEqualChannelFiveReturnMap,
        matchedConnectedReturnTree]
      rw [connectedReturnTree_firstPicardMode]
      exact hCarrier
    · unfold ReturnObservedAtCarrierAndFree
      dsimp only [positiveAllEqualChannelFiveReturnMap,
        matchedConnectedReturnTree]
      simp only [connectedReturnTree_firstPicardMode,
        connectedReturnTree_freeMode]
      exact ⟨hcarrierMode, hmode⟩
  · exact canonicalReturnChannel_connectedReturnTree_allEqual_freeSignOne
      observed q r outerSlot 0 hmode hslot.2

/-- The parameter map is injective on its finite canonical domain.  The
quadratic representative is recovered by canonicalizing the outer vertex;
the eligible distinguished slot is unique; and the stored first-Picard slot
recovers the outer placement. -/
theorem positiveAllEqualChannelFiveReturnMap_injective_on
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    {left right : QuadraticPhaseTerm N × (Fin 2 × Fin 2)}
    (hLeft : left ∈ positiveAllEqualChannelFiveParameters N m observed)
    (hRight : right ∈ positiveAllEqualChannelFiveParameters N m observed)
    (hMap : positiveAllEqualChannelFiveReturnMap observed left =
      positiveAllEqualChannelFiveReturnMap observed right) :
    left = right := by
  have hRaw := congrArg Subtype.val hMap
  change connectedReturnTree observed left.1 left.2.1 left.2.2 0 =
    connectedReturnTree observed right.1 right.2.1 right.2.2 0 at hRaw
  have hRepresentatives := congrArg
    (fun term ↦ canonicalQuadraticSwapRepresentative
      (returnTreeOuterQuadraticTerm term)) hRaw
  rw [canonicalRepresentative_returnTreeOuter_connectedReturnTree,
    canonicalRepresentative_returnTreeOuter_connectedReturnTree]
      at hRepresentatives
  have hLeftParts :=
    (mem_positiveAllEqualChannelFiveParameters_iff
      m observed left).1 hLeft
  have hRightParts :=
    (mem_positiveAllEqualChannelFiveParameters_iff
      m observed right).1 hRight
  have hLeftRepresentative :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed left.1).1 hLeftParts.1 |>.1
  have hRightRepresentative :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed right.1).1 hRightParts.1 |>.1
  rw [(mem_quadraticSwapOrbitRepresentatives_iff left.1).1
        hLeftRepresentative,
      (mem_quadraticSwapOrbitRepresentatives_iff right.1).1
        hRightRepresentative] at hRepresentatives
  have hOuter : left.2.2 = right.2.2 := by
    have hSlot := congrArg iteratedQuadraticFirstPicardSlot hRaw
    simpa only [connectedReturnTree_firstPicardSlot] using hSlot
  have hDistinguished : left.2.1 = right.2.1 := by
    have hRightParts' : right.2.1 ∈
        canonicalAllEqualChannelFiveSlots left.1 := by
      rw [hRepresentatives]
      exact hRightParts.2
    have hAll :=
      (mem_positiveObservedAtBothChildrenRepresentatives_iff
        m observed left.1).1 hLeftParts.1 |>.2.2
    exact canonicalAllEqualChannelFiveSlots_unique left.1
      (hAll.1.symm.trans hAll.2) hLeftParts.2 hRightParts'
  exact Prod.ext hRepresentatives (Prod.ext hDistinguished hOuter)

/-- Finite image of all canonical channel-five parameters. -/
def positiveAllEqualChannelFiveReturnImage
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveAllEqualChannelFiveParameters N m observed).image
    (positiveAllEqualChannelFiveReturnMap observed)

/-- Reading the outer quadratic term of an intrinsic all-equal outer tree
produces a quadratic term with both inputs at the observed mode. -/
theorem observedAtBothChildren_returnTreeOuterQuadraticTerm
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hAll : ReturnObservedAtCarrierAndFree observed term) :
    ObservedAtBothChildren observed (returnTreeOuterQuadraticTerm term) := by
  rcases term with ⟨outerModes, outerSlot, freeSign, innerEntry⟩
  fin_cases outerSlot
  · change observed = outerModes 0 ∧ observed = outerModes 1 at hAll ⊢
    exact hAll
  · change observed = outerModes 1 ∧ observed = outerModes 0 at hAll
    change observed = outerModes 0 ∧ observed = outerModes 1
    exact ⟨hAll.2, hAll.1⟩

/-- The all-equal input-mode predicate is invariant under input swap. -/
@[simp] theorem observedAtBothChildren_swap_iff
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    ObservedAtBothChildren observed (swapQuadraticPhaseTerm q) ↔
      ObservedAtBothChildren observed q := by
  unfold ObservedAtBothChildren
  simp only [swapQuadraticPhaseTerm_mode_zero,
    swapQuadraticPhaseTerm_mode_one]
  tauto

/-- Canonicalizing a swap orbit preserves the all-equal input-mode
predicate. -/
theorem observedAtBothChildren_canonical
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hAll : ObservedAtBothChildren observed q) :
    ObservedAtBothChildren observed
      (canonicalQuadraticSwapRepresentative q) := by
  have hmem := canonicalQuadraticSwapRepresentative_mem_swapOrbit q
  rcases (mem_quadraticSwapOrbit_iff
      (canonicalQuadraticSwapRepresentative q) q).1 hmem with h | h
  · simpa [h] using hAll
  · simpa [h] using hAll

/-- Raw channel five forces binary free sign one. -/
theorem iteratedQuadraticFreeSign_eq_one_of_rawChannelFive
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hFive : InnerZeroObservedInnerOneCancelsFree observed term) :
    iteratedQuadraticFreeSign term = 1 := by
  unfold InnerZeroObservedInnerOneCancelsFree at hFive
  dsimp only at hFive
  have hSign := hFive.1
  unfold iteratedQuadraticFreeSignedLeg binarySignedMode at hSign
  generalize hValue : iteratedQuadraticFreeSign term = sign at hSign ⊢
  fin_cases sign
  · simp [binaryPhaseSign] at hSign
  · rfl

/-- Every member of the surviving selector-five fiber is hit by one
canonical collapsed parameter. -/
theorem exists_positiveAllEqualChannelFiveParameter
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hTerm : term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
      .innerZeroObservedInnerOneCancelsFree) :
    ∃ parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
      positiveAllEqualChannelFiveReturnMap observed parameter = term := by
  classical
  have hFiltered := Finset.mem_filter.mp hTerm
  have hBase := hFiltered.1
  have hLabel := hFiltered.2
  have hBaseParts := Finset.mem_filter.mp hBase
  have hPositiveInner := hBaseParts.1
  have hAllOuter := hBaseParts.2
  have hRaw := canonicalReturnChannel_rawHolds observed term
  rw [hLabel] at hRaw
  have hFive : InnerZeroObservedInnerOneCancelsFree observed term.1 := hRaw
  have hConnected : MatchedIteratedQuadraticConnectedChannel
      observed term.1 := Or.inr (Or.inr (Or.inl hFive))
  obtain ⟨innerSlot, hTree⟩ :=
    exists_innerSlot_connectedReturnTree_eq_of_connectedChannel
      observed term.1 hConnected
  let raw := returnTreeOuterQuadraticTerm term.1
  let q := canonicalQuadraticSwapRepresentative raw
  let slot := iteratedQuadraticFirstPicardSlot term.1
  have hObservedPositive : 0 < modeFrequency m observed := by
    have hInnerPositive :=
      (Finset.mem_filter.mp hPositiveInner).2
    rw [hAllOuter.1]
    exact hInnerPositive
  have hRawAll : ObservedAtBothChildren observed raw :=
    observedAtBothChildren_returnTreeOuterQuadraticTerm
      observed term.1 hAllOuter
  have hQAll : ObservedAtBothChildren observed q :=
    observedAtBothChildren_canonical observed raw hRawAll
  have hQAllAny (input : Fin 2) : observed = q.1 input := by
    fin_cases input
    · exact hQAll.1
    · exact hQAll.2
  have hQPositive : PositiveModeTuple m
      (quadraticCollisionModes observed q) := by
    have hModes : quadraticCollisionModes observed q =
        fun _ ↦ observed := by
      funext leg
      fin_cases leg
      · rfl
      · exact hQAll.1.symm
      · exact hQAll.2.symm
    intro leg
    rw [hModes]
    exact hObservedPositive
  have hQMem : q ∈
      positiveObservedAtBothChildrenRepresentatives N m observed :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed q).2
      ⟨canonicalQuadraticSwapRepresentative_mem_representatives raw,
        hQPositive, hQAll⟩
  have hTermFreeOne : iteratedQuadraticFreeSign term.1 = 1 :=
    iteratedQuadraticFreeSign_eq_one_of_rawChannelFive
      observed term.1 hFive
  have hCanonicalMem :=
    canonicalQuadraticSwapRepresentative_mem_swapOrbit raw
  rcases (mem_quadraticSwapOrbit_iff q raw).1 hCanonicalMem with
      hCanonical | hCanonical
  · have hQTree : connectedReturnTree observed q slot slot innerSlot =
        term.1 := by
      rw [hCanonical]
      exact hTree
    have hFreeOne : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot slot) = 1 := by
      have hFree := congrArg iteratedQuadraticFreeSign hQTree
      simpa only [connectedReturnTree_freeSign, hTermFreeOne] using hFree
    have hMode : observed = q.1 (otherQuadraticSlot slot) :=
      hQAllAny (otherQuadraticSlot slot)
    have hMapAtSlot :
        positiveAllEqualChannelFiveReturnMap
            observed (q, (slot, slot)) = term := by
      apply Subtype.ext
      change connectedReturnTree observed q slot slot 0 = term.1
      exact (connectedReturnTree_innerPlacement_eq_zero_of_allEqual_freeSignOne
        observed q slot slot innerSlot hMode hFreeOne).symm.trans hQTree
    by_cases hFixed : swapQuadraticPhaseTerm q = q
    · have hRepeated : RepeatedChildSameSign q :=
        (swapQuadraticPhaseTerm_eq_self_iff q).1 hFixed
      have hSignConstant (input : Fin 2) :
          quadraticPhaseTermBinarySign q input =
            quadraticPhaseTermBinarySign q 0 := by
        fin_cases input
        · rfl
        · exact hRepeated.2.symm
      have hFreeZero : quadraticPhaseTermBinarySign q
          (otherQuadraticSlot 0) = 1 := by
        calc
          quadraticPhaseTermBinarySign q (otherQuadraticSlot 0) =
              quadraticPhaseTermBinarySign q 0 :=
            hSignConstant (otherQuadraticSlot 0)
          _ = quadraticPhaseTermBinarySign q
              (otherQuadraticSlot slot) :=
            (hSignConstant (otherQuadraticSlot slot)).symm
          _ = 1 := hFreeOne
      have hSlotZero : (0 : Fin 2) ∈
          canonicalAllEqualChannelFiveSlots q := by
        unfold canonicalAllEqualChannelFiveSlots
        apply Finset.mem_filter.mpr
        exact ⟨by simp [canonicalAllEqualDistinguishedSlots, hFixed],
          hFreeZero⟩
      refine ⟨(q, (0, slot)), ?_, ?_⟩
      · exact (mem_positiveAllEqualChannelFiveParameters_iff
          m observed (q, (0, slot))).2 ⟨hQMem, hSlotZero⟩
      · apply Subtype.ext
        have hR := connectedReturnTree_r_eq_zero
          observed q slot slot 0 hRepeated
        exact hR.symm.trans (congrArg Subtype.val hMapAtSlot)
    · have hSlotMem : slot ∈ canonicalAllEqualChannelFiveSlots q := by
        simp [canonicalAllEqualChannelFiveSlots,
          canonicalAllEqualDistinguishedSlots, hFixed, hFreeOne]
      exact ⟨(q, (slot, slot)),
        (mem_positiveAllEqualChannelFiveParameters_iff
          m observed (q, (slot, slot))).2 ⟨hQMem, hSlotMem⟩,
        hMapAtSlot⟩
  · let distinguished := otherQuadraticSlot slot
    have hQTree : connectedReturnTree observed q distinguished slot innerSlot =
        term.1 := by
      dsimp only [distinguished]
      rw [hCanonical, connectedReturnTree_swap_distinguished]
      exact hTree
    have hFreeOne : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot distinguished) = 1 := by
      have hFree := congrArg iteratedQuadraticFreeSign hQTree
      simpa only [connectedReturnTree_freeSign, hTermFreeOne] using hFree
    have hMode : observed =
        q.1 (otherQuadraticSlot distinguished) :=
      hQAllAny (otherQuadraticSlot distinguished)
    have hMapAtDistinguished :
        positiveAllEqualChannelFiveReturnMap
            observed (q, (distinguished, slot)) = term := by
      apply Subtype.ext
      change connectedReturnTree observed q distinguished slot 0 = term.1
      exact (connectedReturnTree_innerPlacement_eq_zero_of_allEqual_freeSignOne
        observed q distinguished slot innerSlot hMode hFreeOne).symm.trans
          hQTree
    by_cases hFixed : swapQuadraticPhaseTerm q = q
    · have hRepeated : RepeatedChildSameSign q :=
        (swapQuadraticPhaseTerm_eq_self_iff q).1 hFixed
      have hSignConstant (input : Fin 2) :
          quadraticPhaseTermBinarySign q input =
            quadraticPhaseTermBinarySign q 0 := by
        fin_cases input
        · rfl
        · exact hRepeated.2.symm
      have hFreeZero : quadraticPhaseTermBinarySign q
          (otherQuadraticSlot 0) = 1 := by
        calc
          quadraticPhaseTermBinarySign q (otherQuadraticSlot 0) =
              quadraticPhaseTermBinarySign q 0 :=
            hSignConstant (otherQuadraticSlot 0)
          _ = quadraticPhaseTermBinarySign q
              (otherQuadraticSlot distinguished) :=
            (hSignConstant (otherQuadraticSlot distinguished)).symm
          _ = 1 := hFreeOne
      have hSlotZero : (0 : Fin 2) ∈
          canonicalAllEqualChannelFiveSlots q := by
        unfold canonicalAllEqualChannelFiveSlots
        apply Finset.mem_filter.mpr
        exact ⟨by simp [canonicalAllEqualDistinguishedSlots, hFixed],
          hFreeZero⟩
      refine ⟨(q, (0, slot)), ?_, ?_⟩
      · exact (mem_positiveAllEqualChannelFiveParameters_iff
          m observed (q, (0, slot))).2 ⟨hQMem, hSlotZero⟩
      · apply Subtype.ext
        have hR := connectedReturnTree_r_eq_zero
          observed q distinguished slot 0 hRepeated
        exact hR.symm.trans (congrArg Subtype.val hMapAtDistinguished)
    · have hSlotMem : distinguished ∈
          canonicalAllEqualChannelFiveSlots q := by
        simp [canonicalAllEqualChannelFiveSlots,
          canonicalAllEqualDistinguishedSlots, hFixed, hFreeOne]
      exact ⟨(q, (distinguished, slot)),
        (mem_positiveAllEqualChannelFiveParameters_iff
          m observed (q, (distinguished, slot))).2 ⟨hQMem, hSlotMem⟩,
        hMapAtDistinguished⟩

/-- The canonical parameter image is exactly the surviving selector-five
fiber. -/
theorem positiveAllEqualChannelFiveReturnImage_eq_channelFive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveAllEqualChannelFiveReturnImage m observed =
      positiveInnerAllEqualOuterCanonicalTerms m observed
        .innerZeroObservedInnerOneCancelsFree := by
  classical
  ext term
  constructor
  · intro hImage
    rcases Finset.mem_image.mp hImage with
      ⟨parameter, hParameter, rfl⟩
    exact positiveAllEqualChannelFiveReturnMap_mem_channelFive
      m observed parameter hParameter
  · intro hTerm
    obtain ⟨parameter, hParameter, hMap⟩ :=
      exists_positiveAllEqualChannelFiveParameter m observed term hTerm
    exact Finset.mem_image.mpr ⟨parameter, hParameter, hMap⟩

/-- Exact global weighted reindex of the surviving selector-five fiber.
This is the multiplicity theorem: each literal tree is counted once by the
canonical parameter set, despite the raw inner-placement collapse. -/
theorem sum_positiveInnerAllEqualOuterChannelFive_eq_parameters
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ positiveInnerAllEqualOuterCanonicalTerms m observed
        .innerZeroObservedInnerOneCancelsFree, weight term) =
      ∑ parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
        weight (positiveAllEqualChannelFiveReturnMap observed parameter) := by
  classical
  rw [← positiveAllEqualChannelFiveReturnImage_eq_channelFive m observed]
  unfold positiveAllEqualChannelFiveReturnImage
  rw [Finset.sum_image]
  intro left hLeft right hRight hMap
  exact positiveAllEqualChannelFiveReturnMap_injective_on
    m observed hLeft hRight hMap

/-- Cardinal form of the exact multiplicity theorem. -/
theorem card_positiveInnerAllEqualOuterChannelFive_eq_parameters
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    (positiveInnerAllEqualOuterCanonicalTerms m observed
      .innerZeroObservedInnerOneCancelsFree).card =
      (positiveAllEqualChannelFiveParameters N m observed).card := by
  classical
  rw [← positiveAllEqualChannelFiveReturnImage_eq_channelFive m observed]
  unfold positiveAllEqualChannelFiveReturnImage
  apply Finset.card_image_of_injOn
  intro left hLeft right hRight hMap
  exact positiveAllEqualChannelFiveReturnMap_injective_on
    m observed hLeft hRight hMap

/-- One canonical channel-five parameter contributes exactly one signed
distinguished-input collision-kernel term. -/
theorem positiveAllEqualChannelFiveReturnMap_feedback_eq_signedKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2))
    (hParameter : parameter ∈
      positiveAllEqualChannelFiveParameters N m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    allEqualPhysicalFeedbackWeight m kappa time energy observed
        (positiveAllEqualChannelFiveReturnMap observed parameter) =
      (quadraticInputInteractionSign parameter.1
          parameter.2.1).coefficient *
        finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign parameter.1) time
          (quadraticCollisionModes observed parameter.1) *
        modeAction energy (modeFrequency m) observed ^ 2 := by
  have hParts :=
    (mem_positiveAllEqualChannelFiveParameters_iff
      m observed parameter).1 hParameter
  have hqParts :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed parameter.1).1 hParts.1
  have hAll := hqParts.2.2
  unfold allEqualPhysicalFeedbackWeight
  change
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed
          (allDistinctConnectedReturnMap observed parameter.1
            (parameter.2.1, parameter.2.2, 0)).1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m
            (allDistinctConnectedReturnMap observed parameter.1
              (parameter.2.1, parameter.2.2, 0)).1) time = _
  rw [allDistinctConnectedReturnMap_feedback_eq_signedKernel_mul_actions
    m kappa time energy observed parameter.1
      (parameter.2.1, parameter.2.2, 0) hEnergy hqParts.2.1]
  simp only [quadraticCollisionSign_succ]
  have hAllAny (input : Fin 2) : observed = parameter.1.1 input := by
    fin_cases input
    · exact hAll.1
    · exact hAll.2
  have hOther : parameter.1.1
      (otherQuadraticSlot parameter.2.1) = observed :=
    (hAllAny (otherQuadraticSlot parameter.2.1)).symm
  rw [hOther]
  ring

/-- The all-equal representative A1 gain is its orbit-cardinality-squared
kernel times the observed action square. -/
theorem positiveObservedAtBothChildrenRepresentativeA1Gain_eq_actionSquare
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveObservedAtBothChildrenRepresentativeA1Gain
        m kappa time energy observed =
      ∑ q ∈ positiveObservedAtBothChildrenRepresentatives N m observed,
        ((quadraticSwapOrbit q).card : Real) ^ 2 *
          finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          modeAction energy (modeFrequency m) observed ^ 2 := by
  classical
  unfold positiveObservedAtBothChildrenRepresentativeA1Gain
    allDistinctLocalA1Gain
  apply Finset.sum_congr rfl
  intro q hq
  have hAll :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed q).1 hq |>.2.2
  simp only [Fin.prod_univ_two]
  rw [← hAll.1, ← hAll.2]
  ring

/-- Exact all-equal gain plus feedback closure.  The first sum is the
coherent A1 gain with its swap-orbit multiplicity; the second is the
surviving signed channel-five correction with the proved global selector
multiplicity.  Tadpole channels one and three do not appear because their
restricted sums were proved zero above. -/
theorem allEqualRepresentativeA1Gain_add_feedback_eq_signedParameters
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveObservedAtBothChildrenRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerObservedAtCarrierAndFreeFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      (∑ q ∈ positiveObservedAtBothChildrenRepresentatives N m observed,
        ((quadraticSwapOrbit q).card : Real) ^ 2 *
          finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          modeAction energy (modeFrequency m) observed ^ 2) +
      ∑ parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
        (quadraticInputInteractionSign parameter.1
            parameter.2.1).coefficient *
          finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign parameter.1) time
            (quadraticCollisionModes observed parameter.1) *
          modeAction energy (modeFrequency m) observed ^ 2 := by
  rw [positiveObservedAtBothChildrenRepresentativeA1Gain_eq_actionSquare,
    positiveInnerObservedAtCarrierAndFreeFeedbackRemainder_eq_channelFive,
    sum_positiveInnerAllEqualOuterChannelFive_eq_parameters]
  apply congrArg (fun value ↦ _ + value)
  apply Finset.sum_congr rfl
  intro parameter hParameter
  exact positiveAllEqualChannelFiveReturnMap_feedback_eq_signedKernel
    m kappa time energy observed parameter hParameter hEnergy

end

end ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
