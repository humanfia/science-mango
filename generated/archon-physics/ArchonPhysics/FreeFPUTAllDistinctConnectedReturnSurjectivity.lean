import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
import ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex

/-!
# Surjectivity of the all-distinct connected-return parametrization

This module reconstructs the ordered quadratic collision term carried by an
arbitrary connected matched return tree.  Canonicalizing that ordered term
under input swap and changing the distinguished input accordingly gives a
literal inverse to the eight-tree constructor on the all-distinct sector.

No positivity or kinetic-limit assertion is involved in the structural
reconstruction.  Positivity is retained separately when the result is
applied to the positive-inner finite fiber.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

@[simp] theorem twoSlotPlacement_self {α : Type*} (slot : Fin 2)
    (values : Fin 2 → α) :
    twoSlotPlacement slot (values slot)
        (values (otherQuadraticSlot slot)) = values := by
  funext input
  fin_cases slot <;> fin_cases input <;>
    simp [twoSlotPlacement, otherQuadraticSlot]

theorem twoSlotPlacement_eq_iff {α : Type*} (slot : Fin 2)
    (selected other : α) (values : Fin 2 → α) :
    twoSlotPlacement slot selected other = values ↔
      selected = values slot ∧
        other = values (otherQuadraticSlot slot) := by
  fin_cases slot
  · constructor
    · intro h
      exact ⟨by simpa [twoSlotPlacement] using congrFun h 0,
        by simpa [twoSlotPlacement, otherQuadraticSlot] using congrFun h 1⟩
    · rintro ⟨hzero, hone⟩
      funext input
      fin_cases input <;> simp [twoSlotPlacement, otherQuadraticSlot, hzero, hone]
  · constructor
    · intro h
      exact ⟨by simpa [twoSlotPlacement] using congrFun h 1,
        by simpa [twoSlotPlacement, otherQuadraticSlot] using congrFun h 0⟩
    · rintro ⟨hone, hzero⟩
      funext input
      fin_cases input <;> simp [twoSlotPlacement, otherQuadraticSlot, hone, hzero]

/-- The ordered quadratic term read directly from the outer vertex of an
iterated quadratic tree.  The `Q1` slot carries the coordinate branch and the
opposite slot carries the free-coordinate sign. -/
def returnTreeOuterQuadraticTerm
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    QuadraticPhaseTerm N :=
  let slot := iteratedQuadraticFirstPicardSlot term
  let signs := twoSlotPlacement slot
    (iteratedQuadraticInnerEntry term).2
    (iteratedQuadraticFreeSign term)
  (iteratedQuadraticOuterModes term, (signs 0, signs 1))

@[simp] theorem returnTreeOuterQuadraticTerm_modes
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (returnTreeOuterQuadraticTerm term).1 =
      iteratedQuadraticOuterModes term := rfl

@[simp] theorem returnTreeOuterQuadraticTerm_sign_selected
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    quadraticPhaseTermBinarySign (returnTreeOuterQuadraticTerm term)
        (iteratedQuadraticFirstPicardSlot term) =
      (iteratedQuadraticInnerEntry term).2 := by
  rcases term with ⟨outerModes, outerSlot, freeSign, innerEntry⟩
  fin_cases outerSlot <;>
    simp [returnTreeOuterQuadraticTerm, quadraticPhaseTermBinarySign,
      twoSlotPlacement, iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticInnerEntry, iteratedQuadraticFreeSign]

@[simp] theorem returnTreeOuterQuadraticTerm_sign_other
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    quadraticPhaseTermBinarySign (returnTreeOuterQuadraticTerm term)
        (otherQuadraticSlot (iteratedQuadraticFirstPicardSlot term)) =
      iteratedQuadraticFreeSign term := by
  rcases term with ⟨outerModes, outerSlot, freeSign, innerEntry⟩
  fin_cases outerSlot <;>
    simp [returnTreeOuterQuadraticTerm, quadraticPhaseTermBinarySign,
      twoSlotPlacement, iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticInnerEntry, iteratedQuadraticFreeSign,
      otherQuadraticSlot]

/-- The three physical modes of a return tree are pairwise distinct. -/
def ConnectedReturnTreeAllDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  iteratedQuadraticFirstPicardMode term ≠ iteratedQuadraticFreeMode term ∧
    observed ≠ iteratedQuadraticFirstPicardMode term ∧
    observed ≠ iteratedQuadraticFreeMode term

/-- Reading the outer vertex of an all-distinct tree produces an
all-distinct quadratic collision term. -/
theorem observedQuadraticAllDistinct_returnTreeOuterQuadraticTerm
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term) :
    ObservedQuadraticAllDistinct observed
      (returnTreeOuterQuadraticTerm term) := by
  unfold ConnectedReturnTreeAllDistinct at hDistinct
  unfold ObservedQuadraticAllDistinct
  rcases term with ⟨outerModes, outerSlot, freeSign, innerEntry⟩
  fin_cases outerSlot
  · change outerModes 0 ≠ outerModes 1 ∧
      observed ≠ outerModes 0 ∧ observed ≠ outerModes 1 at hDistinct
    change outerModes 0 ≠ outerModes 1 ∧
      observed ≠ outerModes 0 ∧ observed ≠ outerModes 1
    exact hDistinct
  · change outerModes 1 ≠ outerModes 0 ∧
      observed ≠ outerModes 1 ∧ observed ≠ outerModes 0 at hDistinct
    change outerModes 0 ≠ outerModes 1 ∧
      observed ≠ outerModes 0 ∧ observed ≠ outerModes 1
    exact ⟨fun h ↦ hDistinct.1 h.symm, hDistinct.2.2, hDistinct.2.1⟩

/-- Every raw connected channel is reconstructed by the outer quadratic term
and one of the two inner observed placements. -/
theorem exists_innerSlot_connectedReturnTree_eq_of_connectedChannel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hConnected : MatchedIteratedQuadraticConnectedChannel observed term) :
    ∃ innerSlot : Fin 2,
      connectedReturnTree observed (returnTreeOuterQuadraticTerm term)
          (iteratedQuadraticFirstPicardSlot term)
          (iteratedQuadraticFirstPicardSlot term) innerSlot = term := by
  rcases term with
    ⟨outerModes, outerSlot, freeSign, ⟨⟨innerModes, innerSignZero,
      innerSignOne⟩, branch⟩⟩
  fin_cases outerSlot <;> fin_cases freeSign <;>
    fin_cases innerSignZero <;> fin_cases innerSignOne <;>
    fin_cases branch <;>
    simp only [MatchedIteratedQuadraticConnectedChannel] at hConnected <;>
    simp [InnerZeroObservedFreeCancelsInnerOne,
      InnerOneObservedFreeCancelsInnerZero,
      InnerZeroObservedInnerOneCancelsFree,
      InnerOneObservedInnerZeroCancelsFree,
      iteratedQuadraticFreeSignedLeg, iteratedQuadraticFreeMode,
      iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticFreeSign, iteratedQuadraticInnerEntry,
      adjustedFirstPicardInnerLeg, quadraticPhaseTermBinarySign,
      coordinateBranchAdjustedBinarySign, binarySignedMode,
      binaryPhaseSign, returnTreeOuterQuadraticTerm,
      connectedReturnTree, connectedReturnOuterModes,
      connectedReturnInnerTerm, connectedReturnInnerModes,
      connectedReturnRawInnerSign, connectedReturnAdjustedInnerSign,
      twoSlotPlacement, otherQuadraticSlot] at hConnected ⊢ <;>
    aesop (config := { warnOnNonterminal := false }) <;>
    simp only [twoSlotPlacement_eq_iff] <;>
    aesop

/-- Simultaneously swapping the ordered quadratic inputs and the
distinguished input leaves the literal connected tree unchanged. -/
@[simp] theorem connectedReturnTree_swap_distinguished
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    connectedReturnTree observed (swapQuadraticPhaseTerm q)
        (otherQuadraticSlot r) outerSlot innerSlot =
      connectedReturnTree observed q r outerSlot innerSlot := by
  rcases q with ⟨modes, signZero, signOne⟩
  fin_cases r <;> fin_cases outerSlot <;> fin_cases innerSlot <;>
    fin_cases signZero <;> fin_cases signOne <;>
    simp [connectedReturnTree, connectedReturnOuterModes,
      connectedReturnInnerTerm, connectedReturnInnerModes,
      connectedReturnRawInnerSign, connectedReturnAdjustedInnerSign,
      swapQuadraticPhaseTerm, quadraticInputSlotSwap,
      quadraticPhaseTermBinarySign, coordinateBranchAdjustedBinarySign,
      twoSlotPlacement, otherQuadraticSlot]

/-- All-distinctness is invariant under exchange of the two ordered
quadratic inputs. -/
@[simp] theorem observedQuadraticAllDistinct_swap_iff
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    ObservedQuadraticAllDistinct observed (swapQuadraticPhaseTerm q) ↔
      ObservedQuadraticAllDistinct observed q := by
  unfold ObservedQuadraticAllDistinct
  simp only [swapQuadraticPhaseTerm_mode_zero,
    swapQuadraticPhaseTerm_mode_one]
  tauto

/-- The canonical representative itself is a member of the representative
finset. -/
@[simp] theorem canonicalQuadraticSwapRepresentative_mem_representatives
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) :
    canonicalQuadraticSwapRepresentative q ∈
      quadraticSwapOrbitRepresentatives N := by
  exact (mem_quadraticSwapOrbitRepresentatives_iff _).2
    (canonicalQuadraticSwapRepresentative_idempotent q)

/-- Canonicalization preserves the all-distinct collision sector. -/
theorem observedQuadraticAllDistinct_canonical
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    ObservedQuadraticAllDistinct observed
      (canonicalQuadraticSwapRepresentative q) := by
  have hmem := canonicalQuadraticSwapRepresentative_mem_swapOrbit q
  rcases (mem_quadraticSwapOrbit_iff
      (canonicalQuadraticSwapRepresentative q) q).1 hmem with h | h
  · simpa [h] using hDistinct
  · simpa [h] using hDistinct

/-- A connected matched tree in the all-distinct sector belongs to the
literal eight-tree image of a canonical swap-orbit representative. -/
theorem exists_canonicalRepresentative_index_eq_of_allDistinct_connected
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1)
    (hConnected : MatchedIteratedQuadraticConnectedChannel observed term.1) :
    ∃ q : QuadraticPhaseTerm N,
      q ∈ quadraticSwapOrbitRepresentatives N ∧
      ObservedQuadraticAllDistinct observed q ∧
      ∃ index : AllDistinctConnectedReturnIndex,
        allDistinctConnectedReturnMap observed q index = term := by
  let raw := returnTreeOuterQuadraticTerm term.1
  let q := canonicalQuadraticSwapRepresentative raw
  have hRawDistinct : ObservedQuadraticAllDistinct observed raw :=
    observedQuadraticAllDistinct_returnTreeOuterQuadraticTerm
      observed term.1 hDistinct
  obtain ⟨innerSlot, htree⟩ :=
    exists_innerSlot_connectedReturnTree_eq_of_connectedChannel
      observed term.1 hConnected
  refine ⟨q, canonicalQuadraticSwapRepresentative_mem_representatives raw,
    observedQuadraticAllDistinct_canonical observed raw hRawDistinct, ?_⟩
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

/-- Reading the outer quadratic term back from a constructed tree returns a
member of the original term's two-element swap orbit. -/
theorem returnTreeOuterQuadraticTerm_connectedReturnTree_mem_swapOrbit
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    returnTreeOuterQuadraticTerm
        (connectedReturnTree observed q r outerSlot innerSlot) ∈
      quadraticSwapOrbit q := by
  rw [mem_quadraticSwapOrbit_iff]
  rcases q with ⟨modes, signZero, signOne⟩
  fin_cases r <;> fin_cases outerSlot
  · left
    apply Prod.ext
    · funext input
      fin_cases input <;>
        simp [returnTreeOuterQuadraticTerm, connectedReturnTree,
          connectedReturnOuterModes, iteratedQuadraticOuterModes,
          iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry,
          iteratedQuadraticFreeSign, twoSlotPlacement, otherQuadraticSlot]
    · simp [returnTreeOuterQuadraticTerm, connectedReturnTree,
        connectedReturnOuterModes, iteratedQuadraticOuterModes,
        iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry,
        iteratedQuadraticFreeSign, twoSlotPlacement, otherQuadraticSlot]
  · right
    apply Prod.ext
    · funext input
      fin_cases input <;>
        simp [returnTreeOuterQuadraticTerm, connectedReturnTree,
          connectedReturnOuterModes, iteratedQuadraticOuterModes,
          iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry,
          iteratedQuadraticFreeSign, twoSlotPlacement, otherQuadraticSlot,
          swapQuadraticPhaseTerm, quadraticInputSlotSwap]
    · simp [returnTreeOuterQuadraticTerm, connectedReturnTree,
        connectedReturnOuterModes, iteratedQuadraticOuterModes,
        iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry,
        iteratedQuadraticFreeSign, twoSlotPlacement, otherQuadraticSlot,
        swapQuadraticPhaseTerm]
  · right
    apply Prod.ext
    · funext input
      fin_cases input <;>
        simp [returnTreeOuterQuadraticTerm, connectedReturnTree,
          connectedReturnOuterModes, iteratedQuadraticOuterModes,
          iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry,
          iteratedQuadraticFreeSign, twoSlotPlacement, otherQuadraticSlot,
          swapQuadraticPhaseTerm, quadraticInputSlotSwap]
    · simp [returnTreeOuterQuadraticTerm, connectedReturnTree,
        connectedReturnOuterModes, iteratedQuadraticOuterModes,
        iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry,
        iteratedQuadraticFreeSign, twoSlotPlacement, otherQuadraticSlot,
        swapQuadraticPhaseTerm]
  · left
    apply Prod.ext
    · funext input
      fin_cases input <;>
        simp [returnTreeOuterQuadraticTerm, connectedReturnTree,
          connectedReturnOuterModes, iteratedQuadraticOuterModes,
          iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry,
          iteratedQuadraticFreeSign, twoSlotPlacement, otherQuadraticSlot]
    · simp [returnTreeOuterQuadraticTerm, connectedReturnTree,
        connectedReturnOuterModes, iteratedQuadraticOuterModes,
        iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry,
        iteratedQuadraticFreeSign, twoSlotPlacement, otherQuadraticSlot]

/-- Consequently, reading and canonicalizing a constructed outer term gives
the same representative as canonicalizing the constructor input. -/
theorem canonicalRepresentative_returnTreeOuter_connectedReturnTree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    canonicalQuadraticSwapRepresentative
        (returnTreeOuterQuadraticTerm
          (connectedReturnTree observed q r outerSlot innerSlot)) =
      canonicalQuadraticSwapRepresentative q := by
  exact canonicalQuadraticSwapRepresentative_eq_of_mem_swapOrbit
    (returnTreeOuterQuadraticTerm_connectedReturnTree_mem_swapOrbit
      observed q r outerSlot innerSlot)

/-- Canonical representative and local index are jointly unique in the
all-distinct sector.  This is the cross-representative injectivity that the
local eight-tree module intentionally did not assert. -/
theorem canonicalRepresentative_localIndex_unique
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (qLeft qRight : QuadraticPhaseTerm N)
    (hLeftRep : qLeft ∈ quadraticSwapOrbitRepresentatives N)
    (hRightRep : qRight ∈ quadraticSwapOrbitRepresentatives N)
    (hLeftDistinct : ObservedQuadraticAllDistinct observed qLeft)
    (left right : AllDistinctConnectedReturnIndex)
    (heq : allDistinctConnectedReturnMap observed qLeft left =
      allDistinctConnectedReturnMap observed qRight right) :
    qLeft = qRight ∧ left = right := by
  have htree :
      connectedReturnTree observed qLeft left.1 left.2.1 left.2.2 =
        connectedReturnTree observed qRight right.1 right.2.1 right.2.2 :=
    congrArg Subtype.val heq
  have houter := congrArg
    (fun term ↦ canonicalQuadraticSwapRepresentative
      (returnTreeOuterQuadraticTerm term)) htree
  rw [canonicalRepresentative_returnTreeOuter_connectedReturnTree,
    canonicalRepresentative_returnTreeOuter_connectedReturnTree,
    (mem_quadraticSwapOrbitRepresentatives_iff qLeft).1 hLeftRep,
    (mem_quadraticSwapOrbitRepresentatives_iff qRight).1 hRightRep] at houter
  subst qRight
  refine ⟨rfl, allDistinctConnectedReturnMap_injective
    observed qLeft hLeftDistinct ?_⟩
  exact heq

/-- A constructor value is all-distinct whenever its collision term is. -/
theorem connectedReturnTree_allDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    ConnectedReturnTreeAllDistinct observed
      (connectedReturnTree observed q r outerSlot innerSlot) := by
  unfold ConnectedReturnTreeAllDistinct
  simp only [connectedReturnTree_firstPicardMode,
    connectedReturnTree_freeMode]
  fin_cases r
  · exact hDistinct
  · exact ⟨fun h ↦ hDistinct.1 h.symm,
      hDistinct.2.2, hDistinct.2.1⟩

/-- Canonical swap representative together with one of its eight local
connected-return indices. -/
abbrev CanonicalAllDistinctConnectedReturnParameter
    (N : Nat) [NeZero N] (observed : Lattice.Site N) :=
  {parameter : QuadraticPhaseTerm N × AllDistinctConnectedReturnIndex //
    parameter.1 ∈ quadraticSwapOrbitRepresentatives N ∧
      ObservedQuadraticAllDistinct observed parameter.1}

/-- The exact all-distinct connected part of the matched return-tree type. -/
abbrev AllDistinctConnectedMatchedReturnTerm
    (N : Nat) [NeZero N] (observed : Lattice.Site N) :=
  {term : FreeInitialMatchedIteratedQuadraticTerm N observed //
    ConnectedReturnTreeAllDistinct observed term.1 ∧
      MatchedIteratedQuadraticConnectedChannel observed term.1}

/-- Global constructor from canonical parameters to all-distinct connected
matched trees. -/
def canonicalAllDistinctConnectedReturnMap
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    CanonicalAllDistinctConnectedReturnParameter N observed →
      AllDistinctConnectedMatchedReturnTerm N observed :=
  fun parameter ↦
    ⟨allDistinctConnectedReturnMap observed
        parameter.1.1 parameter.1.2,
      connectedReturnTree_allDistinct observed parameter.1.1
        parameter.1.2.1 parameter.1.2.2.1 parameter.1.2.2.2
        parameter.2.2,
      allDistinctConnectedReturnMap_connectedChannel observed
        parameter.1.1 parameter.1.2⟩

@[simp] theorem canonicalAllDistinctConnectedReturnMap_val
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (parameter : CanonicalAllDistinctConnectedReturnParameter N observed) :
    (canonicalAllDistinctConnectedReturnMap observed parameter).1 =
      allDistinctConnectedReturnMap observed
        parameter.1.1 parameter.1.2 := rfl

/-- The global canonical constructor is injective, including across
different raw quadratic terms. -/
theorem canonicalAllDistinctConnectedReturnMap_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    Function.Injective
      (canonicalAllDistinctConnectedReturnMap observed) := by
  intro left right heq
  have hmap :
      allDistinctConnectedReturnMap observed left.1.1 left.1.2 =
        allDistinctConnectedReturnMap observed right.1.1 right.1.2 :=
    congrArg Subtype.val heq
  have hunique := canonicalRepresentative_localIndex_unique observed
    left.1.1 right.1.1 left.2.1 right.2.1 left.2.2
    left.1.2 right.1.2 hmap
  apply Subtype.ext
  exact Prod.ext hunique.1 hunique.2

/-- Every all-distinct connected matched tree is hit by the global canonical
constructor. -/
theorem canonicalAllDistinctConnectedReturnMap_surjective
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    Function.Surjective
      (canonicalAllDistinctConnectedReturnMap observed) := by
  intro target
  obtain ⟨q, hRepresentative, hDistinct, index, heq⟩ :=
    exists_canonicalRepresentative_index_eq_of_allDistinct_connected
      observed target.1 target.2.1 target.2.2
  let parameter : CanonicalAllDistinctConnectedReturnParameter N observed :=
    ⟨(q, index), hRepresentative, hDistinct⟩
  refine ⟨parameter, ?_⟩
  apply Subtype.ext
  exact heq

/-- Exact equivalence between canonical collision parameters and the full
all-distinct connected matched-tree sector. -/
def canonicalAllDistinctConnectedReturnEquiv
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    CanonicalAllDistinctConnectedReturnParameter N observed ≃
      AllDistinctConnectedMatchedReturnTerm N observed :=
  Equiv.ofBijective (canonicalAllDistinctConnectedReturnMap observed)
    ⟨canonicalAllDistinctConnectedReturnMap_injective observed,
      canonicalAllDistinctConnectedReturnMap_surjective observed⟩

/-- Explicit inverse requested by the global reindex: it recovers the unique
canonical quadratic representative and unique local binary triple. -/
def canonicalAllDistinctConnectedReturnInverse
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    AllDistinctConnectedMatchedReturnTerm N observed →
      CanonicalAllDistinctConnectedReturnParameter N observed :=
  (canonicalAllDistinctConnectedReturnEquiv observed).symm

@[simp] theorem canonicalMap_inverse
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : AllDistinctConnectedMatchedReturnTerm N observed) :
    canonicalAllDistinctConnectedReturnMap observed
        (canonicalAllDistinctConnectedReturnInverse observed term) = term :=
  (canonicalAllDistinctConnectedReturnEquiv observed).apply_symm_apply term

@[simp] theorem canonicalInverse_map
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (parameter : CanonicalAllDistinctConnectedReturnParameter N observed) :
    canonicalAllDistinctConnectedReturnInverse observed
        (canonicalAllDistinctConnectedReturnMap observed parameter) =
      parameter :=
  (canonicalAllDistinctConnectedReturnEquiv observed).symm_apply_apply parameter

@[simp] theorem canonicalAllDistinctConnectedReturnMap_firstPicardMode
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (parameter : CanonicalAllDistinctConnectedReturnParameter N observed) :
    iteratedQuadraticFirstPicardMode
        (canonicalAllDistinctConnectedReturnMap observed parameter).1.1 =
      parameter.1.1.1 parameter.1.2.1 := by
  exact connectedReturnTree_firstPicardMode observed parameter.1.1
    parameter.1.2.1 parameter.1.2.2.1 parameter.1.2.2.2

/-- Canonical parameters restricted to a positive inner carrier. -/
abbrev PositiveCanonicalAllDistinctConnectedReturnParameter
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  {parameter : CanonicalAllDistinctConnectedReturnParameter N observed //
    0 < modeFrequency m
      (parameter.1.1.1 parameter.1.2.1)}

/-- All-distinct connected matched trees with a positive inner carrier. -/
abbrev PositiveAllDistinctConnectedMatchedReturnTerm
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  {term : AllDistinctConnectedMatchedReturnTerm N observed //
    0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term.1.1)}

/-- Restriction of the global constructor to the positive-inner sector. -/
def positiveCanonicalAllDistinctConnectedReturnMap
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveCanonicalAllDistinctConnectedReturnParameter N m observed →
      PositiveAllDistinctConnectedMatchedReturnTerm N m observed :=
  fun parameter ↦
    ⟨canonicalAllDistinctConnectedReturnMap observed parameter.1,
      by simpa using parameter.2⟩

/-- The positive-inner canonical constructor remains injective. -/
theorem positiveCanonicalAllDistinctConnectedReturnMap_injective
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Function.Injective
      (positiveCanonicalAllDistinctConnectedReturnMap m observed) := by
  intro left right heq
  apply Subtype.ext
  apply canonicalAllDistinctConnectedReturnMap_injective observed
  exact congrArg Subtype.val heq

/-- Every positive-inner all-distinct connected matched tree has a canonical
representative and a unique local index. -/
theorem positiveCanonicalAllDistinctConnectedReturnMap_surjective
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Function.Surjective
      (positiveCanonicalAllDistinctConnectedReturnMap m observed) := by
  intro target
  obtain ⟨parameter, heq⟩ :=
    canonicalAllDistinctConnectedReturnMap_surjective observed target.1
  have hmode := congrArg
    (fun term : AllDistinctConnectedMatchedReturnTerm N observed ↦
      iteratedQuadraticFirstPicardMode term.1.1) heq
  have hPositive :
      0 < modeFrequency m
        (parameter.1.1.1 parameter.1.2.1) := by
    rw [← canonicalAllDistinctConnectedReturnMap_firstPicardMode
      observed parameter, hmode]
    exact target.2
  refine ⟨⟨parameter, hPositive⟩, ?_⟩
  apply Subtype.ext
  exact heq

/-- Exact positive-inner version of the global reconstruction equivalence. -/
def positiveCanonicalAllDistinctConnectedReturnEquiv
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveCanonicalAllDistinctConnectedReturnParameter N m observed ≃
      PositiveAllDistinctConnectedMatchedReturnTerm N m observed :=
  Equiv.ofBijective
    (positiveCanonicalAllDistinctConnectedReturnMap m observed)
    ⟨positiveCanonicalAllDistinctConnectedReturnMap_injective m observed,
      positiveCanonicalAllDistinctConnectedReturnMap_surjective m observed⟩

/-- The inverse on precisely the positive-inner sector used by the physical
feedback sum. -/
def positiveCanonicalAllDistinctConnectedReturnInverse
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveAllDistinctConnectedMatchedReturnTerm N m observed →
      PositiveCanonicalAllDistinctConnectedReturnParameter N m observed :=
  (positiveCanonicalAllDistinctConnectedReturnEquiv m observed).symm

@[simp] theorem positiveCanonicalMap_inverse
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : PositiveAllDistinctConnectedMatchedReturnTerm N m observed) :
    positiveCanonicalAllDistinctConnectedReturnMap m observed
        (positiveCanonicalAllDistinctConnectedReturnInverse
          m observed term) = term :=
  (positiveCanonicalAllDistinctConnectedReturnEquiv m observed).apply_symm_apply
    term

/-- The positive subtype is exactly supported by the previously established
positive-inner finset, not a new positivity convention. -/
theorem positiveAllDistinctConnectedMatchedReturnTerm_mem_positiveInner
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : PositiveAllDistinctConnectedMatchedReturnTerm N m observed) :
    term.1.1 ∈ positiveInnerMatchedIteratedQuadraticTerms m observed := by
  classical
  simp [positiveInnerMatchedIteratedQuadraticTerms, term.2]

end

end ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
