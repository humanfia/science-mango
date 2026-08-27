import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
import ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel

/-!
# Canonical selector fibers on the all-distinct connected-return sector

The six raw return predicates can overlap when modes coincide.  On the
all-distinct sector the two free-observed (tadpole) predicates are impossible:
the free mode is required both to equal and to differ from the observed mode.
Consequently the first-match canonical selector lands in exactly the four
connected labels.

This module bridges that statement to the finite positive-inner fibers used
by the physical feedback sum.  It does not claim raw-channel disjointness
outside the all-distinct sector.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- The four selector labels whose observed copy is carried by an inner leg. -/
def canonicalConnectedReturnChannels : Finset CanonicalReturnChannel :=
  { .innerZeroObservedFreeCancelsInnerOne,
    .innerOneObservedFreeCancelsInnerZero,
    .innerZeroObservedInnerOneCancelsFree,
    .innerOneObservedInnerZeroCancelsFree }

/-- Membership in the four-label set is equivalently exclusion of the two
free-observed labels. -/
@[simp] theorem mem_canonicalConnectedReturnChannels_iff
    (channel : CanonicalReturnChannel) :
    channel ∈ canonicalConnectedReturnChannels ↔
      channel ≠ .freeObservedInnerZeroCancelsInnerOne ∧
        channel ≠ .freeObservedInnerOneCancelsInnerZero := by
  cases channel <;> simp [canonicalConnectedReturnChannels]

/-- All-distinctness rules out the first raw tadpole predicate. -/
theorem not_freeObservedInnerZeroCancelsInnerOne_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term) :
    ¬ FreeObservedInnerZeroCancelsInnerOne observed term := by
  intro hTadpole
  rcases hTadpole with ⟨_, _, _, hFreeObserved, _⟩
  have hFreeMode : iteratedQuadraticFreeMode term = observed := by
    simpa [iteratedQuadraticFreeSignedLeg, binarySignedMode] using
      hFreeObserved
  exact hDistinct.2.2 hFreeMode.symm

/-- All-distinctness rules out the second raw tadpole predicate. -/
theorem not_freeObservedInnerOneCancelsInnerZero_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term) :
    ¬ FreeObservedInnerOneCancelsInnerZero observed term := by
  intro hTadpole
  rcases hTadpole with ⟨_, _, _, hFreeObserved, _⟩
  have hFreeMode : iteratedQuadraticFreeMode term = observed := by
    simpa [iteratedQuadraticFreeSignedLeg, binarySignedMode] using
      hFreeObserved
  exact hDistinct.2.2 hFreeMode.symm

/-- In particular an all-distinct return tree is not in either raw tadpole
channel. -/
theorem not_tadpole_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term) :
    ¬ MatchedIteratedQuadraticTadpoleChannel observed term := by
  intro hTadpole
  rcases hTadpole with hTadpole | hTadpole
  · exact not_freeObservedInnerZeroCancelsInnerOne_of_allDistinct
      observed term hDistinct hTadpole
  · exact not_freeObservedInnerOneCancelsInnerZero_of_allDistinct
      observed term hDistinct hTadpole

/-- `RawHolds` formulation of exclusion of the first tadpole label. -/
theorem not_firstTadpole_rawHolds_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term) :
    ¬ CanonicalReturnChannel.RawHolds
        .freeObservedInnerZeroCancelsInnerOne observed term := by
  simpa only [CanonicalReturnChannel.RawHolds] using
    not_freeObservedInnerZeroCancelsInnerOne_of_allDistinct
      observed term hDistinct

/-- `RawHolds` formulation of exclusion of the second tadpole label. -/
theorem not_secondTadpole_rawHolds_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term) :
    ¬ CanonicalReturnChannel.RawHolds
        .freeObservedInnerOneCancelsInnerZero observed term := by
  simpa only [CanonicalReturnChannel.RawHolds] using
    not_freeObservedInnerOneCancelsInnerZero_of_allDistinct
      observed term hDistinct

/-- The disjoint first-match priority predicate for the first tadpole label
is impossible on the all-distinct sector. -/
theorem not_firstTadpole_priorityHolds_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term) :
    ¬ CanonicalReturnChannel.PriorityHolds
        .freeObservedInnerZeroCancelsInnerOne observed term := by
  intro hPriority
  exact not_firstTadpole_rawHolds_of_allDistinct observed term hDistinct
    hPriority.rawHolds

/-- The disjoint first-match priority predicate for the second tadpole label
is impossible on the all-distinct sector. -/
theorem not_secondTadpole_priorityHolds_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term) :
    ¬ CanonicalReturnChannel.PriorityHolds
        .freeObservedInnerOneCancelsInnerZero observed term := by
  intro hPriority
  exact not_secondTadpole_rawHolds_of_allDistinct observed term hDistinct
    hPriority.rawHolds

/-- Six-way charge completeness therefore reduces to a connected raw
channel for every all-distinct matched tree. -/
theorem connectedChannel_of_allDistinct_matched
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1) :
    MatchedIteratedQuadraticConnectedChannel observed term.1 := by
  rcases matchedIteratedQuadratic_tadpole_or_connected
      observed term.1 term.2 with hTadpole | hConnected
  · exact (not_tadpole_of_allDistinct observed term.1 hDistinct
      hTadpole).elim
  · exact hConnected

/-- The first-match selector cannot choose the first tadpole label on the
all-distinct sector. -/
theorem canonicalReturnChannel_ne_firstTadpole_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1) :
    canonicalReturnChannel observed term ≠
      .freeObservedInnerZeroCancelsInnerOne := by
  intro hChannel
  have hRaw := canonicalReturnChannel_rawHolds observed term
  rw [hChannel] at hRaw
  exact not_freeObservedInnerZeroCancelsInnerOne_of_allDistinct
    observed term.1 hDistinct hRaw

/-- The first-match selector cannot choose the second tadpole label on the
all-distinct sector. -/
theorem canonicalReturnChannel_ne_secondTadpole_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1) :
    canonicalReturnChannel observed term ≠
      .freeObservedInnerOneCancelsInnerZero := by
  intro hChannel
  have hRaw := canonicalReturnChannel_rawHolds observed term
  rw [hChannel] at hRaw
  exact not_freeObservedInnerOneCancelsInnerZero_of_allDistinct
    observed term.1 hDistinct hRaw

/-- Exact selector statement: an all-distinct matched tree lands in the
four-label connected set. -/
theorem canonicalReturnChannel_mem_connected_of_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1) :
    canonicalReturnChannel observed term ∈
      canonicalConnectedReturnChannels := by
  rw [mem_canonicalConnectedReturnChannels_iff]
  exact ⟨canonicalReturnChannel_ne_firstTadpole_of_allDistinct
      observed term hDistinct,
    canonicalReturnChannel_ne_secondTadpole_of_allDistinct
      observed term hDistinct⟩

/-- On the all-distinct matched sector, the raw connected predicate is
equivalent to selection of one of the four connected labels.  The reverse
direction follows from selector soundness; the forward direction uses the
all-distinct exclusion of both earlier tadpole labels. -/
theorem connectedChannel_iff_canonicalReturnChannel_mem
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1) :
    MatchedIteratedQuadraticConnectedChannel observed term.1 ↔
      canonicalReturnChannel observed term ∈
        canonicalConnectedReturnChannels := by
  constructor
  · intro _hConnected
    exact canonicalReturnChannel_mem_connected_of_allDistinct
      observed term hDistinct
  · intro hChannel
    have hRaw := canonicalReturnChannel_rawHolds observed term
    rw [mem_canonicalConnectedReturnChannels_iff] at hChannel
    cases hSelected : canonicalReturnChannel observed term <;>
      simp_all [CanonicalReturnChannel.RawHolds,
        MatchedIteratedQuadraticConnectedChannel]

/-- The finite positive-inner sector restricted only by all-distinctness.
Matched charge completeness makes every element a connected return tree by
`connectedChannel_of_allDistinct_matched`. -/
def positiveInnerAllDistinctConnectedReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveInnerMatchedIteratedQuadraticTerms m observed).filter
    fun term ↦ ConnectedReturnTreeAllDistinct observed term.1

@[simp] theorem mem_positiveInnerAllDistinctConnectedReturnTerms_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed ↔
      term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed ∧
        ConnectedReturnTreeAllDistinct observed term.1 := by
  classical
  simp [positiveInnerAllDistinctConnectedReturnTerms]

/-- One original positive-inner canonical selector fiber, restricted to the
all-distinct sector. -/
def positiveInnerAllDistinctCanonicalReturnChannelTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (channel : CanonicalReturnChannel) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveInnerCanonicalReturnChannelTerms m observed channel).filter
    fun term ↦ ConnectedReturnTreeAllDistinct observed term.1

/-- The first tadpole selector fiber is empty after imposing
all-distinctness. -/
theorem positiveInnerAllDistinct_firstTadpoleFiber_eq_empty
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerAllDistinctCanonicalReturnChannelTerms m observed
        .freeObservedInnerZeroCancelsInnerOne = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro term hTerm
  have hFiltered := Finset.mem_filter.mp hTerm
  have hFiber := Finset.mem_filter.mp hFiltered.1
  exact canonicalReturnChannel_ne_firstTadpole_of_allDistinct
    observed term hFiltered.2 hFiber.2

/-- The second tadpole selector fiber is empty after imposing
all-distinctness. -/
theorem positiveInnerAllDistinct_secondTadpoleFiber_eq_empty
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerAllDistinctCanonicalReturnChannelTerms m observed
        .freeObservedInnerOneCancelsInnerZero = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro term hTerm
  have hFiltered := Finset.mem_filter.mp hTerm
  have hFiber := Finset.mem_filter.mp hFiltered.1
  exact canonicalReturnChannel_ne_secondTadpole_of_allDistinct
    observed term hFiltered.2 hFiber.2

/-- The filtered fiber is literally the selector fiber of the finite
all-distinct base. -/
theorem positiveInnerAllDistinctCanonicalReturnChannelTerms_eq_fiber
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (channel : CanonicalReturnChannel) :
    positiveInnerAllDistinctCanonicalReturnChannelTerms
        m observed channel =
      canonicalReturnChannelFiber observed
        (positiveInnerAllDistinctConnectedReturnTerms m observed)
        channel := by
  classical
  ext term
  simp [positiveInnerAllDistinctCanonicalReturnChannelTerms,
    positiveInnerCanonicalReturnChannelTerms,
    canonicalReturnChannelFiber,
    positiveInnerAllDistinctConnectedReturnTerms,
    and_left_comm, and_comm]

/-- Membership bridge stated directly with the original positive-inner
canonical fibers.  The explicit all-distinct conjunct is essential because
those original fibers also contain repeated-mode boundary strata. -/
theorem mem_positiveInnerAllDistinctConnectedReturnTerms_iff_originalFibers
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed ↔
      ConnectedReturnTreeAllDistinct observed term.1 ∧
        ∃ channel ∈ canonicalConnectedReturnChannels,
          term ∈ positiveInnerCanonicalReturnChannelTerms
            m observed channel := by
  classical
  constructor
  · intro hTerm
    have hParts :=
      (mem_positiveInnerAllDistinctConnectedReturnTerms_iff
        m observed term).1 hTerm
    refine ⟨hParts.2, canonicalReturnChannel observed term, ?_, ?_⟩
    · exact canonicalReturnChannel_mem_connected_of_allDistinct
        observed term hParts.2
    · unfold positiveInnerCanonicalReturnChannelTerms
        canonicalReturnChannelFiber
      exact Finset.mem_filter.mpr ⟨hParts.1, rfl⟩
  · rintro ⟨hDistinct, channel, _hConnectedLabel, hFiber⟩
    apply (mem_positiveInnerAllDistinctConnectedReturnTerms_iff
      m observed term).2
    refine ⟨?_, hDistinct⟩
    exact (Finset.mem_filter.mp hFiber).1

/-- Equivalent membership statement using the four already-filtered,
pairwise disjoint selector fibers. -/
theorem mem_positiveInnerAllDistinctConnectedReturnTerms_iff_filteredFibers
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed ↔
      ∃ channel ∈ canonicalConnectedReturnChannels,
        term ∈ positiveInnerAllDistinctCanonicalReturnChannelTerms
          m observed channel := by
  classical
  constructor
  · intro hTerm
    have hDistinct :=
      (mem_positiveInnerAllDistinctConnectedReturnTerms_iff
        m observed term).1 hTerm |>.2
    refine ⟨canonicalReturnChannel observed term,
      canonicalReturnChannel_mem_connected_of_allDistinct
        observed term hDistinct, ?_⟩
    rw [positiveInnerAllDistinctCanonicalReturnChannelTerms_eq_fiber]
    exact Finset.mem_filter.mpr ⟨hTerm, rfl⟩
  · rintro ⟨channel, _hChannel, hTerm⟩
    rw [positiveInnerAllDistinctCanonicalReturnChannelTerms_eq_fiber]
      at hTerm
    exact (Finset.mem_filter.mp hTerm).1

/-- Every finite positive-inner all-distinct term is represented by the
existing positive all-distinct connected matched subtype, and conversely. -/
theorem mem_positiveInnerAllDistinctConnectedReturnTerms_iff_exists_subtype
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed ↔
      ∃ connected : PositiveAllDistinctConnectedMatchedReturnTerm
          N m observed,
        connected.1.1 = term := by
  classical
  constructor
  · intro hTerm
    have hParts :=
      (mem_positiveInnerAllDistinctConnectedReturnTerms_iff
        m observed term).1 hTerm
    have hPositive :
        0 < modeFrequency m
          (iteratedQuadraticFirstPicardMode term.1) := by
      simpa [positiveInnerMatchedIteratedQuadraticTerms] using hParts.1
    let connected : PositiveAllDistinctConnectedMatchedReturnTerm
        N m observed :=
      ⟨⟨term, hParts.2,
          connectedChannel_of_allDistinct_matched
            observed term hParts.2⟩,
        hPositive⟩
    exact ⟨connected, rfl⟩
  · rintro ⟨connected, rfl⟩
    apply (mem_positiveInnerAllDistinctConnectedReturnTerms_iff
      m observed connected.1.1).2
    refine ⟨?_, connected.1.2.1⟩
    simpa [positiveInnerMatchedIteratedQuadraticTerms] using connected.2

/-- Exact weighted partition of the all-distinct positive-inner sector into
the four canonical connected selector fibers. -/
theorem sum_positiveInnerAllDistinctConnectedReturnTerms_eq_fourFibers
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ positiveInnerAllDistinctConnectedReturnTerms m observed,
        weight term) =
      ∑ channel ∈ canonicalConnectedReturnChannels,
        ∑ term ∈ positiveInnerAllDistinctCanonicalReturnChannelTerms
            m observed channel,
          weight term := by
  classical
  simp_rw [positiveInnerAllDistinctCanonicalReturnChannelTerms_eq_fiber]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := positiveInnerAllDistinctConnectedReturnTerms m observed)
    (t := canonicalConnectedReturnChannels)
    (g := canonicalReturnChannel observed)
    (fun term hTerm ↦
      canonicalReturnChannel_mem_connected_of_allDistinct observed term
        ((mem_positiveInnerAllDistinctConnectedReturnTerms_iff
          m observed term).1 hTerm).2)
    weight]
  rfl

end

end ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber
