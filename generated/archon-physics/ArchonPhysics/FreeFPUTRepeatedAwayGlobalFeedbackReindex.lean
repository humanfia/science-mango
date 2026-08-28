import ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
import ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
import ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge

/-!
# Global reindex of the repeated-child-away FPUT feedback

The tree-level repeated-away feedback is indexed by the original canonical
matched-tree base.  This module safely reindexes that base by canonical
quadratic swap representatives.  Equal child signs give the four-tree local
image, while opposite child signs give the eight-tree local image.

The proof reconstructs the outer quadratic term of every matched tree and
proves disjointness across distinct canonical representatives.  In
particular, no fixed-`q` image is assumed to be a global fiber.
-/

namespace ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection
open ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.SignedThreeWaveCollisionFlux
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-! ## Intrinsic sign split -/

/-- Repeated-away trees whose reconstructed outer quadratic children have
the same binary sign. -/
def positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveInnerCarrierFreeRepeatedAwayReturnTerms m observed).filter
    fun term ↦ RepeatedChildSameSign
      (returnTreeOuterQuadraticTerm term.1)

/-- Repeated-away trees whose reconstructed outer quadratic children have
opposite binary signs. -/
def positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveInnerCarrierFreeRepeatedAwayReturnTerms m observed).filter
    fun term ↦ RepeatedChildOppositeSign
      (returnTreeOuterQuadraticTerm term.1)

/-- Literal union of the two sign strata, with its classical equality
instance hidden from theorem signatures. -/
def positiveInnerCarrierFreeRepeatedAwaySignReturnTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms m observed ∪
    positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms m observed

@[simp] theorem mem_positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms
        m observed ↔
      term ∈ positiveInnerCarrierFreeRepeatedAwayReturnTerms m observed ∧
        RepeatedChildSameSign (returnTreeOuterQuadraticTerm term.1) := by
  classical
  simp [positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms]

@[simp] theorem mem_positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms
        m observed ↔
      term ∈ positiveInnerCarrierFreeRepeatedAwayReturnTerms m observed ∧
        RepeatedChildOppositeSign
          (returnTreeOuterQuadraticTerm term.1) := by
  classical
  simp [positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms]

/-- The intrinsic repeated-away base is exactly split by equality of the two
reconstructed child signs. -/
theorem positiveInnerCarrierFreeRepeatedAwayReturnTerms_eq_sign_union
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveInnerCarrierFreeRepeatedAwayReturnTerms m observed =
      positiveInnerCarrierFreeRepeatedAwaySignReturnTerms m observed := by
  classical
  unfold positiveInnerCarrierFreeRepeatedAwaySignReturnTerms
  ext term
  simp only [Finset.mem_union,
    mem_positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_iff,
    mem_positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_iff]
  constructor
  · intro hTerm
    have hAway := (Finset.mem_filter.mp hTerm).2
    have hSelectedOther :
        (returnTreeOuterQuadraticTerm term.1).1
              (iteratedQuadraticFirstPicardSlot term.1) =
          (returnTreeOuterQuadraticTerm term.1).1
            (otherQuadraticSlot
              (iteratedQuadraticFirstPicardSlot term.1)) := by
      rw [returnTreeOuterQuadraticTerm_selectedMode,
        returnTreeOuterQuadraticTerm_otherMode]
      exact hAway.1
    have hModes :
        (returnTreeOuterQuadraticTerm term.1).1 0 =
          (returnTreeOuterQuadraticTerm term.1).1 1 := by
      generalize hslot : iteratedQuadraticFirstPicardSlot term.1 = slot at hSelectedOther
      fin_cases slot
      · simpa [otherQuadraticSlot] using hSelectedOther
      · simpa [otherQuadraticSlot] using hSelectedOther.symm
    by_cases hSigns :
        (returnTreeOuterQuadraticTerm term.1).2.1 =
          (returnTreeOuterQuadraticTerm term.1).2.2
    · exact Or.inl ⟨hTerm, hModes, hSigns⟩
    · exact Or.inr ⟨hTerm, hModes, hSigns⟩
  · rintro (⟨hTerm, _⟩ | ⟨hTerm, _⟩) <;> exact hTerm

theorem positiveInnerCarrierFreeRepeatedAway_sign_disjoint
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Disjoint
      (positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms m observed)
      (positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms
        m observed) := by
  classical
  rw [Finset.disjoint_left]
  intro term hSame hOpposite
  have hs :=
    (mem_positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_iff
      m observed term).1 hSame |>.2.2
  have ho :=
    (mem_positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_iff
      m observed term).1 hOpposite |>.2.2
  exact ho hs

/-! ## Safe canonical reconstruction -/

/-- A repeated-away matched tree cannot be a tadpole, because every raw
tadpole has its free mode equal to the observed mode. -/
theorem connectedChannel_of_carrierFreeRepeatedAway_matched
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hAway : ReturnCarrierFreeRepeatedAwayFromObserved observed term.1) :
    MatchedIteratedQuadraticConnectedChannel observed term.1 := by
  rcases matchedIteratedQuadratic_tadpole_or_connected
      observed term.1 term.2 with hTadpole | hConnected
  · exfalso
    rcases hTadpole with hTadpole | hTadpole
    · rcases hTadpole with ⟨_, _, _, hFreeObserved, _⟩
      have hFree : iteratedQuadraticFreeMode term.1 = observed := by
        simpa [iteratedQuadraticFreeSignedLeg, binarySignedMode] using
          hFreeObserved
      exact hAway.2 (hAway.1.trans hFree).symm
    · rcases hTadpole with ⟨_, _, _, hFreeObserved, _⟩
      have hFree : iteratedQuadraticFreeMode term.1 = observed := by
        simpa [iteratedQuadraticFreeSignedLeg, binarySignedMode] using
          hFreeObserved
      exact hAway.2 (hAway.1.trans hFree).symm
  · exact hConnected

/-- Every connected matched tree, without any mode-distinctness assumption,
is produced by the eight-index constructor for the canonicalized outer
quadratic term. -/
theorem exists_canonicalRepresentative_index_eq_of_connected
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hConnected : MatchedIteratedQuadraticConnectedChannel observed term.1) :
    ∃ q : QuadraticPhaseTerm N,
      q ∈ quadraticSwapOrbitRepresentatives N ∧
        ∃ index : AllDistinctConnectedReturnIndex,
          allDistinctConnectedReturnMap observed q index = term := by
  let raw := returnTreeOuterQuadraticTerm term.1
  let q := canonicalQuadraticSwapRepresentative raw
  obtain ⟨innerSlot, htree⟩ :=
    exists_innerSlot_connectedReturnTree_eq_of_connectedChannel
      observed term.1 hConnected
  refine ⟨q, canonicalQuadraticSwapRepresentative_mem_representatives raw, ?_⟩
  have hmem := canonicalQuadraticSwapRepresentative_mem_swapOrbit raw
  rcases (mem_quadraticSwapOrbit_iff q raw).1 hmem with hcanonical | hcanonical
  · refine ⟨(iteratedQuadraticFirstPicardSlot term.1,
        iteratedQuadraticFirstPicardSlot term.1, innerSlot), ?_⟩
    apply Subtype.ext
    change connectedReturnTree observed q
        (iteratedQuadraticFirstPicardSlot term.1)
        (iteratedQuadraticFirstPicardSlot term.1) innerSlot = term.1
    rw [hcanonical]
    exact htree
  · refine ⟨(otherQuadraticSlot
          (iteratedQuadraticFirstPicardSlot term.1),
        iteratedQuadraticFirstPicardSlot term.1, innerSlot), ?_⟩
    apply Subtype.ext
    change connectedReturnTree observed q
        (otherQuadraticSlot (iteratedQuadraticFirstPicardSlot term.1))
        (iteratedQuadraticFirstPicardSlot term.1) innerSlot = term.1
    rw [hcanonical, connectedReturnTree_swap_distinguished]
    exact htree

/-- Local connected images belonging to distinct canonical representatives
are disjoint.  This is the cross-`q` fact needed before applying
`Finset.sum_biUnion`. -/
theorem allDistinctConnectedReturnImage_disjoint_of_canonical_ne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (qLeft qRight : QuadraticPhaseTerm N)
    (hLeft : qLeft ∈ quadraticSwapOrbitRepresentatives N)
    (hRight : qRight ∈ quadraticSwapOrbitRepresentatives N)
    (hne : qLeft ≠ qRight) :
    Disjoint (allDistinctConnectedReturnImage observed qLeft)
      (allDistinctConnectedReturnImage observed qRight) := by
  classical
  rw [Finset.disjoint_left]
  intro term hTermLeft hTermRight
  rcases Finset.mem_image.mp hTermLeft with ⟨left, _hleft, hleft⟩
  rcases Finset.mem_image.mp hTermRight with ⟨right, _hright, hright⟩
  have htree :
      allDistinctConnectedReturnMap observed qLeft left =
        allDistinctConnectedReturnMap observed qRight right :=
    hleft.trans hright.symm
  have hraw := congrArg
    (fun mapped : FreeInitialMatchedIteratedQuadraticTerm N observed ↦
      canonicalQuadraticSwapRepresentative
        (returnTreeOuterQuadraticTerm mapped.1)) htree
  simp only [allDistinctConnectedReturnMap_val,
    canonicalRepresentative_returnTreeOuter_connectedReturnTree,
    (mem_quadraticSwapOrbitRepresentatives_iff qLeft).1 hLeft,
    (mem_quadraticSwapOrbitRepresentatives_iff qRight).1 hRight] at hraw
  exact hne hraw

/-! ## Global same-sign fiber -/

@[simp] theorem repeatedChildSameSign_swap_iff
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) :
    RepeatedChildSameSign (swapQuadraticPhaseTerm q) ↔
      RepeatedChildSameSign q := by
  unfold RepeatedChildSameSign
  simp only [swapQuadraticPhaseTerm_mode_zero,
    swapQuadraticPhaseTerm_mode_one,
    swapQuadraticPhaseTerm_leftSign,
    swapQuadraticPhaseTerm_rightSign]
  constructor <;> rintro ⟨hmodes, hsigns⟩
  · exact ⟨hmodes.symm, hsigns.symm⟩
  · exact ⟨hmodes.symm, hsigns.symm⟩

@[simp] theorem repeatedChildOppositeSign_swap_iff
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) :
    RepeatedChildOppositeSign (swapQuadraticPhaseTerm q) ↔
      RepeatedChildOppositeSign q := by
  unfold RepeatedChildOppositeSign
  simp only [swapQuadraticPhaseTerm_mode_zero,
    swapQuadraticPhaseTerm_mode_one,
    swapQuadraticPhaseTerm_leftSign,
    swapQuadraticPhaseTerm_rightSign]
  constructor <;> rintro ⟨hmodes, hsigns⟩
  · exact ⟨hmodes.symm, fun h ↦ hsigns h.symm⟩
  · exact ⟨hmodes.symm, fun h ↦ hsigns h.symm⟩

theorem repeatedChildSameSign_iff_of_mem_swapOrbit
    {N : Nat} [NeZero N] {candidate q : QuadraticPhaseTerm N}
    (hmem : candidate ∈ quadraticSwapOrbit q) :
    RepeatedChildSameSign candidate ↔ RepeatedChildSameSign q := by
  rcases (mem_quadraticSwapOrbit_iff candidate q).1 hmem with h | h
  · rw [h]
  · rw [h, repeatedChildSameSign_swap_iff]

theorem repeatedChildOppositeSign_iff_of_mem_swapOrbit
    {N : Nat} [NeZero N] {candidate q : QuadraticPhaseTerm N}
    (hmem : candidate ∈ quadraticSwapOrbit q) :
    RepeatedChildOppositeSign candidate ↔
      RepeatedChildOppositeSign q := by
  rcases (mem_quadraticSwapOrbit_iff candidate q).1 hmem with h | h
  · rw [h]
  · rw [h, repeatedChildOppositeSign_swap_iff]

theorem repeatedChild_mode_other_eq
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hModes : q.1 0 = q.1 1) :
    q.1 (otherQuadraticSlot r) = q.1 r := by
  fin_cases r
  · simpa using hModes.symm
  · simpa using hModes

theorem repeatedChild_mode_eq_zero
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hModes : q.1 0 = q.1 1) :
    q.1 r = q.1 0 := by
  fin_cases r
  · rfl
  · exact hModes.symm

theorem observedSeparatedRepeatedChildSameSign_of_away_outer
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hAway : ReturnCarrierFreeRepeatedAwayFromObserved observed term)
    (hSame : RepeatedChildSameSign
      (returnTreeOuterQuadraticTerm term)) :
    ObservedSeparatedRepeatedChildSameSign observed
      (returnTreeOuterQuadraticTerm term) := by
  refine ⟨hSame, ?_⟩
  intro hObserved
  have hSelected :
      observed = (returnTreeOuterQuadraticTerm term).1
        (iteratedQuadraticFirstPicardSlot term) := by
    generalize hslot : iteratedQuadraticFirstPicardSlot term = slot
    fin_cases slot
    · simpa [hslot] using hObserved
    · exact hObserved.trans hSame.1
  rw [returnTreeOuterQuadraticTerm_selectedMode] at hSelected
  exact hAway.2 hSelected

theorem observedSeparatedRepeatedChildOppositeSign_of_away_outer
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hAway : ReturnCarrierFreeRepeatedAwayFromObserved observed term)
    (hOpposite : RepeatedChildOppositeSign
      (returnTreeOuterQuadraticTerm term)) :
    ObservedSeparatedRepeatedChildOppositeSign observed
      (returnTreeOuterQuadraticTerm term) := by
  refine ⟨hOpposite, ?_⟩
  intro hObserved
  have hSelected :
      observed = (returnTreeOuterQuadraticTerm term).1
        (iteratedQuadraticFirstPicardSlot term) := by
    generalize hslot : iteratedQuadraticFirstPicardSlot term = slot
    fin_cases slot
    · simpa [hslot] using hObserved
    · exact hObserved.trans hOpposite.1
  rw [returnTreeOuterQuadraticTerm_selectedMode] at hSelected
  exact hAway.2 hSelected

/-- Union of all same-sign local images over the positive canonical base,
with classical finite-set equality hidden from theorem signatures. -/
def positiveRepeatedChildSameSignConnectedReturnImages
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveRepeatedChildSameSignRepresentatives N m observed).biUnion
    (allDistinctConnectedReturnImage observed)

/-- The same-sign tree base is the disjoint union of the literal local
images over positive canonical same-sign representatives. -/
theorem positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_eq_biUnion
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms m observed =
      positiveRepeatedChildSameSignConnectedReturnImages m observed := by
  classical
  unfold positiveRepeatedChildSameSignConnectedReturnImages
  ext term
  constructor
  · intro hTerm
    have hParts :=
      (mem_positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_iff
        m observed term).1 hTerm
    have hAway := (Finset.mem_filter.mp hParts.1).2
    have hConnected :=
      connectedChannel_of_carrierFreeRepeatedAway_matched
        observed term hAway
    obtain ⟨q, hRepresentative, index, hmap⟩ :=
      exists_canonicalRepresentative_index_eq_of_connected
        observed term hConnected
    have hOuterOrbit :
        returnTreeOuterQuadraticTerm term.1 ∈ quadraticSwapOrbit q := by
      have hLocal :=
        returnTreeOuterQuadraticTerm_connectedReturnTree_mem_swapOrbit
          observed q index.1 index.2.1 index.2.2
      have hmapVal := congrArg Subtype.val hmap
      rw [← hmapVal]
      exact hLocal
    have hSame : RepeatedChildSameSign q :=
      (repeatedChildSameSign_iff_of_mem_swapOrbit hOuterOrbit).1 hParts.2
    have hSeparated : ObservedSeparatedRepeatedChildSameSign observed q := by
      refine ⟨hSame, ?_⟩
      intro hObservedChild
      have hFirstMode := congrArg
        (fun mapped : FreeInitialMatchedIteratedQuadraticTerm N observed ↦
          iteratedQuadraticFirstPicardMode mapped.1) hmap
      have hTermInner :
          iteratedQuadraticFirstPicardMode term.1 =
            iteratedQuadraticFreeMode term.1 := hAway.1
      have hqSelected : q.1 index.1 = observed :=
        (repeatedChild_mode_eq_zero q index.1 hSame.1).trans
          hObservedChild.symm
      have hqFree : q.1 (otherQuadraticSlot index.1) = observed :=
        (repeatedChild_mode_other_eq q index.1 hSame.1).trans hqSelected
      have hTermFree := congrArg
        (fun mapped : FreeInitialMatchedIteratedQuadraticTerm N observed ↦
          iteratedQuadraticFreeMode mapped.1) hmap
      have : iteratedQuadraticFreeMode term.1 = observed := by
        rw [← hTermFree, allDistinctConnectedReturnMap_val,
          connectedReturnTree_freeMode, hqFree]
      exact hAway.2 (hTermInner.trans this).symm
    have hInner :
        0 < modeFrequency m (iteratedQuadraticFirstPicardMode term.1) := by
      have hPositiveBase := (Finset.mem_filter.mp hParts.1).1
      simpa [positiveInnerMatchedIteratedQuadraticTerms] using hPositiveBase
    have hFirstMode := congrArg
      (fun mapped : FreeInitialMatchedIteratedQuadraticTerm N observed ↦
        iteratedQuadraticFirstPicardMode mapped.1) hmap
    have hSelected : 0 < modeFrequency m (q.1 index.1) := by
      have hFirstMode' :
          q.1 index.1 = iteratedQuadraticFirstPicardMode term.1 := by
        simpa only [allDistinctConnectedReturnMap_val,
          connectedReturnTree_firstPicardMode] using hFirstMode
      rw [hFirstMode']
      exact hInner
    have hOther :
        0 < modeFrequency m (q.1 (otherQuadraticSlot index.1)) := by
      rw [repeatedChild_mode_other_eq q index.1 hSame.1]
      exact hSelected
    have hPositive :
        PositiveModeTuple m (quadraticCollisionModes observed q) :=
      positiveModeTuple_quadraticCollisionModes_of_selected_other
        m observed q index.1 hObserved hSelected hOther
    have hq : q ∈ positiveRepeatedChildSameSignRepresentatives
        N m observed :=
      (mem_positiveRepeatedChildSameSignRepresentatives_iff
        m observed q).2 ⟨by
          exact Finset.mem_filter.mpr ⟨hRepresentative, hPositive⟩,
        hSeparated⟩
    have hImage := allDistinctConnectedReturnMap_mem_image observed q index
    rw [hmap] at hImage
    exact Finset.mem_biUnion.mpr ⟨q, hq, hImage⟩
  · intro hTerm
    rcases Finset.mem_biUnion.mp hTerm with ⟨q, hq, hImage⟩
    rcases Finset.mem_image.mp hImage with ⟨index, _hindex, hmap⟩
    have hqParts :=
      (mem_positiveRepeatedChildSameSignRepresentatives_iff
        m observed q).1 hq
    have hRepeated := hqParts.2.1
    have hPositive := (Finset.mem_filter.mp hqParts.1).2
    rw [← hmap]
    apply
      (mem_positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_iff
        m observed _).2
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · simp only [positiveInnerMatchedIteratedQuadraticTerms,
          Finset.mem_filter, Finset.mem_univ, true_and,
          allDistinctConnectedReturnMap_val,
          connectedReturnTree_firstPicardMode]
        simpa [quadraticCollisionModes] using hPositive (Fin.succ index.1)
      · unfold ReturnCarrierFreeRepeatedAwayFromObserved
        simp only [allDistinctConnectedReturnMap_val,
          connectedReturnTree_firstPicardMode,
          connectedReturnTree_freeMode]
        constructor
        · exact (repeatedChild_mode_other_eq
            q index.1 hRepeated.1).symm
        · intro hObservedSelected
          apply hqParts.2.2
          rw [← repeatedChild_mode_eq_zero q index.1 hRepeated.1]
          exact hObservedSelected
    · apply (repeatedChildSameSign_iff_of_mem_swapOrbit
          (returnTreeOuterQuadraticTerm_connectedReturnTree_mem_swapOrbit
            observed q index.1 index.2.1 index.2.2)).2
      exact hRepeated

/-! ## Global opposite-sign fiber -/

/-- Union of all opposite-sign local images over the positive canonical
base, with classical finite-set equality hidden from theorem signatures. -/
def positiveRepeatedChildOppositeSignConnectedReturnImages
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact
    (positiveRepeatedChildOppositeSignRepresentatives N m observed).biUnion
      (allDistinctConnectedReturnImage observed)

/-- The opposite-sign tree base is the disjoint union of the literal local
images over positive canonical opposite-sign representatives. -/
theorem positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_eq_biUnion
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms m observed =
      positiveRepeatedChildOppositeSignConnectedReturnImages m observed := by
  classical
  unfold positiveRepeatedChildOppositeSignConnectedReturnImages
  ext term
  constructor
  · intro hTerm
    have hParts :=
      (mem_positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_iff
        m observed term).1 hTerm
    have hAway := (Finset.mem_filter.mp hParts.1).2
    have hConnected :=
      connectedChannel_of_carrierFreeRepeatedAway_matched
        observed term hAway
    obtain ⟨q, hRepresentative, index, hmap⟩ :=
      exists_canonicalRepresentative_index_eq_of_connected
        observed term hConnected
    have hOuterOrbit :
        returnTreeOuterQuadraticTerm term.1 ∈ quadraticSwapOrbit q := by
      have hLocal :=
        returnTreeOuterQuadraticTerm_connectedReturnTree_mem_swapOrbit
          observed q index.1 index.2.1 index.2.2
      have hmapVal := congrArg Subtype.val hmap
      rw [← hmapVal]
      exact hLocal
    have hOpposite : RepeatedChildOppositeSign q :=
      (repeatedChildOppositeSign_iff_of_mem_swapOrbit hOuterOrbit).1
        hParts.2
    have hSeparated :
        ObservedSeparatedRepeatedChildOppositeSign observed q := by
      refine ⟨hOpposite, ?_⟩
      intro hObservedChild
      have hTermInner :
          iteratedQuadraticFirstPicardMode term.1 =
            iteratedQuadraticFreeMode term.1 := hAway.1
      have hqSelected : q.1 index.1 = observed :=
        (repeatedChild_mode_eq_zero q index.1 hOpposite.1).trans
          hObservedChild.symm
      have hqFree : q.1 (otherQuadraticSlot index.1) = observed :=
        (repeatedChild_mode_other_eq q index.1 hOpposite.1).trans hqSelected
      have hTermFree := congrArg
        (fun mapped : FreeInitialMatchedIteratedQuadraticTerm N observed ↦
          iteratedQuadraticFreeMode mapped.1) hmap
      have : iteratedQuadraticFreeMode term.1 = observed := by
        rw [← hTermFree, allDistinctConnectedReturnMap_val,
          connectedReturnTree_freeMode, hqFree]
      exact hAway.2 (hTermInner.trans this).symm
    have hInner :
        0 < modeFrequency m (iteratedQuadraticFirstPicardMode term.1) := by
      have hPositiveBase := (Finset.mem_filter.mp hParts.1).1
      simpa [positiveInnerMatchedIteratedQuadraticTerms] using hPositiveBase
    have hFirstMode := congrArg
      (fun mapped : FreeInitialMatchedIteratedQuadraticTerm N observed ↦
        iteratedQuadraticFirstPicardMode mapped.1) hmap
    have hSelected : 0 < modeFrequency m (q.1 index.1) := by
      have hFirstMode' :
          q.1 index.1 = iteratedQuadraticFirstPicardMode term.1 := by
        simpa only [allDistinctConnectedReturnMap_val,
          connectedReturnTree_firstPicardMode] using hFirstMode
      rw [hFirstMode']
      exact hInner
    have hOther :
        0 < modeFrequency m (q.1 (otherQuadraticSlot index.1)) := by
      rw [repeatedChild_mode_other_eq q index.1 hOpposite.1]
      exact hSelected
    have hPositive :
        PositiveModeTuple m (quadraticCollisionModes observed q) :=
      positiveModeTuple_quadraticCollisionModes_of_selected_other
        m observed q index.1 hObserved hSelected hOther
    have hq : q ∈ positiveRepeatedChildOppositeSignRepresentatives
        N m observed :=
      (mem_positiveRepeatedChildOppositeSignRepresentatives_iff
        m observed q).2 ⟨by
          exact Finset.mem_filter.mpr ⟨hRepresentative, hPositive⟩,
        hSeparated⟩
    have hImage := allDistinctConnectedReturnMap_mem_image observed q index
    rw [hmap] at hImage
    exact Finset.mem_biUnion.mpr ⟨q, hq, hImage⟩
  · intro hTerm
    rcases Finset.mem_biUnion.mp hTerm with ⟨q, hq, hImage⟩
    rcases Finset.mem_image.mp hImage with ⟨index, _hindex, hmap⟩
    have hqParts :=
      (mem_positiveRepeatedChildOppositeSignRepresentatives_iff
        m observed q).1 hq
    have hRepeated := hqParts.2.1
    have hPositive := (Finset.mem_filter.mp hqParts.1).2
    rw [← hmap]
    apply
      (mem_positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_iff
        m observed _).2
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · simp only [positiveInnerMatchedIteratedQuadraticTerms,
          Finset.mem_filter, Finset.mem_univ, true_and,
          allDistinctConnectedReturnMap_val,
          connectedReturnTree_firstPicardMode]
        simpa [quadraticCollisionModes] using hPositive (Fin.succ index.1)
      · unfold ReturnCarrierFreeRepeatedAwayFromObserved
        simp only [allDistinctConnectedReturnMap_val,
          connectedReturnTree_firstPicardMode,
          connectedReturnTree_freeMode]
        constructor
        · exact (repeatedChild_mode_other_eq
            q index.1 hRepeated.1).symm
        · intro hObservedSelected
          apply hqParts.2.2
          rw [← repeatedChild_mode_eq_zero q index.1 hRepeated.1]
          exact hObservedSelected
    · apply (repeatedChildOppositeSign_iff_of_mem_swapOrbit
          (returnTreeOuterQuadraticTerm_connectedReturnTree_mem_swapOrbit
            observed q index.1 index.2.1 index.2.2)).2
      exact hRepeated

/-! ## Physical weighted reindex and local gain--loss closure -/

/-- Physical tree feedback on the same-sign repeated-away stratum. -/
def positiveInnerCarrierFreeRepeatedAwaySameSignFeedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ term ∈ positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms
      m observed,
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Physical tree feedback on the opposite-sign repeated-away stratum. -/
def positiveInnerCarrierFreeRepeatedAwayOppositeSignFeedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ term ∈ positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms
      m observed,
    compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Exact intrinsic sign partition of the original tree-level
repeated-away feedback. -/
theorem positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder_eq_sign_partition
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder
        m kappa time radius observed =
      positiveInnerCarrierFreeRepeatedAwaySameSignFeedback
          m kappa time radius observed +
        positiveInnerCarrierFreeRepeatedAwayOppositeSignFeedback
          m kappa time radius observed := by
  classical
  unfold positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder
    positiveInnerCarrierFreeRepeatedAwaySameSignFeedback
    positiveInnerCarrierFreeRepeatedAwayOppositeSignFeedback
  rw [positiveInnerCarrierFreeRepeatedAwayReturnTerms_eq_sign_union]
  unfold positiveInnerCarrierFreeRepeatedAwaySignReturnTerms
  exact Finset.sum_union
    (positiveInnerCarrierFreeRepeatedAway_sign_disjoint m observed)

theorem positiveRepeatedChildSameSign_localImages_pairwiseDisjoint
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Set.PairwiseDisjoint
      (↑(positiveRepeatedChildSameSignRepresentatives N m observed))
      (allDistinctConnectedReturnImage observed) := by
  classical
  intro q hq right hright hne
  have hq' : q ∈ positiveRepeatedChildSameSignRepresentatives
      N m observed := by simpa using hq
  have hright' : right ∈ positiveRepeatedChildSameSignRepresentatives
      N m observed := by simpa using hright
  have hqRep :=
    (Finset.mem_filter.mp
      ((mem_positiveRepeatedChildSameSignRepresentatives_iff
        m observed q).1 hq').1).1
  have hrightRep :=
    (Finset.mem_filter.mp
      ((mem_positiveRepeatedChildSameSignRepresentatives_iff
        m observed right).1 hright').1).1
  exact allDistinctConnectedReturnImage_disjoint_of_canonical_ne
    observed q right hqRep hrightRep hne

theorem positiveRepeatedChildOppositeSign_localImages_pairwiseDisjoint
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Set.PairwiseDisjoint
      (↑(positiveRepeatedChildOppositeSignRepresentatives N m observed))
      (allDistinctConnectedReturnImage observed) := by
  classical
  intro q hq right hright hne
  have hq' : q ∈ positiveRepeatedChildOppositeSignRepresentatives
      N m observed := by simpa using hq
  have hright' : right ∈ positiveRepeatedChildOppositeSignRepresentatives
      N m observed := by simpa using hright
  have hqRep :=
    (Finset.mem_filter.mp
      ((mem_positiveRepeatedChildOppositeSignRepresentatives_iff
        m observed q).1 hq').1).1
  have hrightRep :=
    (Finset.mem_filter.mp
      ((mem_positiveRepeatedChildOppositeSignRepresentatives_iff
        m observed right).1 hright').1).1
  exact allDistinctConnectedReturnImage_disjoint_of_canonical_ne
    observed q right hqRep hrightRep hne

/-- The original same-sign tree feedback is exactly the sum of the existing
four-tree local feedbacks, once for every positive canonical representative. -/
theorem positiveInnerCarrierFreeRepeatedAwaySameSignFeedback_eq_local
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerCarrierFreeRepeatedAwaySameSignFeedback m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      ∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
        repeatedChildConnectedReturnFeedbackSum
          m kappa time energy observed q := by
  classical
  unfold positiveInnerCarrierFreeRepeatedAwaySameSignFeedback
  rw [positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_eq_biUnion
    m observed hObserved]
  unfold positiveRepeatedChildSameSignConnectedReturnImages
  rw [Finset.sum_biUnion
    (positiveRepeatedChildSameSign_localImages_pairwiseDisjoint m observed)]
  apply Finset.sum_congr rfl
  intro q hq
  have hRepeated :=
    ((mem_positiveRepeatedChildSameSignRepresentatives_iff
      m observed q).1 hq).2.1
  unfold repeatedChildConnectedReturnFeedbackSum
  rw [allDistinctConnectedReturnImage_eq_repeatedChildImage
    observed q hRepeated]

/-- The original opposite-sign tree feedback is exactly the sum of the
existing eight-tree local feedbacks, once for every positive canonical
representative. -/
theorem positiveInnerCarrierFreeRepeatedAwayOppositeSignFeedback_eq_local
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerCarrierFreeRepeatedAwayOppositeSignFeedback m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      ∑ q ∈ positiveRepeatedChildOppositeSignRepresentatives N m observed,
        repeatedChildOppositeSignConnectedReturnFeedbackSum
          m kappa time energy observed q := by
  classical
  unfold positiveInnerCarrierFreeRepeatedAwayOppositeSignFeedback
  rw [positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_eq_biUnion
    m observed hObserved]
  unfold positiveRepeatedChildOppositeSignConnectedReturnImages
  rw [Finset.sum_biUnion
    (positiveRepeatedChildOppositeSign_localImages_pairwiseDisjoint
      m observed)]
  rfl

/-- Exact global reindex of the complete repeated-away feedback into the
same-sign four-tree and opposite-sign eight-tree local sums. -/
theorem positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder_eq_local
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      (∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
        repeatedChildConnectedReturnFeedbackSum
          m kappa time energy observed q) +
      ∑ q ∈ positiveRepeatedChildOppositeSignRepresentatives
          N m observed,
        repeatedChildOppositeSignConnectedReturnFeedbackSum
          m kappa time energy observed q := by
  rw [
    positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder_eq_sign_partition,
    positiveInnerCarrierFreeRepeatedAwaySameSignFeedback_eq_local
      m kappa time energy observed hObserved,
    positiveInnerCarrierFreeRepeatedAwayOppositeSignFeedback_eq_local
      m kappa time energy observed hObserved]

/-- Adding the two representative A1 gains to the original repeated-away
tree feedback produces the sum of the already-proved local gain--feedback
expressions, with no missing or duplicated tree. -/
theorem repeatedAwayRepresentativeA1Gain_add_feedback_eq_local
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveRepeatedChildSameSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveRepeatedChildOppositeSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      (∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
        repeatedChildSameSignLocalGainFeedback
          m kappa time energy observed q) +
      ∑ q ∈ positiveRepeatedChildOppositeSignRepresentatives
          N m observed,
        repeatedChildOppositeSignLocalGainFeedback
          m kappa time energy observed q := by
  rw [positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder_eq_local
    m kappa time energy observed hObserved]
  unfold positiveRepeatedChildSameSignRepresentativeA1Gain
    positiveRepeatedChildOppositeSignRepresentativeA1Gain
    repeatedChildSameSignLocalGainFeedback
    repeatedChildOppositeSignLocalGainFeedback
  simp only [Finset.sum_add_distrib]
  ring

/-- Fully evaluated repeated-away gain--loss identity.  The same-sign
fixed-point sector retains its exact two-copy correction, while the
opposite-sign sector is four copies of its signed flux. -/
def repeatedChildSameSignSignedFluxWithCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
      quadraticSignedCollisionFlux q
        (modeAction energy (modeFrequency m)) observed +
    2 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
      (quadraticInputInteractionSign q 0).coefficient *
      modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m) (q.1 0)

def repeatedChildOppositeSignFourSignedFlux
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  4 * finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q) *
      quadraticSignedCollisionFlux q
        (modeAction energy (modeFrequency m)) observed

theorem repeatedAwayRepresentativeA1Gain_add_feedback_eq_signedFlux
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveRepeatedChildSameSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveRepeatedChildOppositeSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      (∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
        repeatedChildSameSignSignedFluxWithCorrection
          m kappa time energy observed q) +
      ∑ q ∈ positiveRepeatedChildOppositeSignRepresentatives
          N m observed,
        repeatedChildOppositeSignFourSignedFlux
          m kappa time energy observed q := by
  classical
  rw [repeatedAwayRepresentativeA1Gain_add_feedback_eq_local
    m kappa time energy observed hObserved]
  congr 1
  · apply Finset.sum_congr rfl
    intro q hq
    have hqParts :=
      (mem_positiveRepeatedChildSameSignRepresentatives_iff
        m observed q).1 hq
    simpa only [repeatedChildSameSignSignedFluxWithCorrection] using
      (repeatedChildSameSignLocalGainFeedback_eq_signedFlux_add_correction
        m kappa time energy observed q hqParts.2 hEnergy
          (Finset.mem_filter.mp hqParts.1).2)
  · apply Finset.sum_congr rfl
    intro q hq
    have hqParts :=
      (mem_positiveRepeatedChildOppositeSignRepresentatives_iff
        m observed q).1 hq
    simpa only [repeatedChildOppositeSignFourSignedFlux] using
      (repeatedChildOppositeSignLocalGainFeedback_eq_four_signedFlux
        m kappa time energy observed q hqParts.2 hEnergy
          (Finset.mem_filter.mp hqParts.1).2)

end

end ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex
