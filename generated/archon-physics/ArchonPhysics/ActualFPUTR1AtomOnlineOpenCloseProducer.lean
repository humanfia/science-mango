import ArchonPhysics.ActualFPUTR1OnlineCompletedCellTransition

/-!
# Atom-level hole-to-root open/close producer for an actual R1 fine fibre

The completed-cell adapter scans the order in which completed cells happen
to be listed.  That order is useful for finite regrouping, but it is not an
online stopping construction: atoms belonging to one porous dependency block
can be interleaved with atoms belonging to another block.

This file instead reverses the exact indexed fine atom word and scans that
literal word from hole to root.  At every atom position it emits an `open` or
`read` event.  As soon as the already-scanned prefix contains every atom of
the current maximal porous block, it emits one additional `close` event at
the same atom position.  Thus an `A-B-A` word keeps both owners open in the
generic keyed multi-open state.

The event retains the original fine-history index, the literal atom
position, the atom, its coefficient-complete owner, and the owner payload
visible in the scanned prefix.  The structural payment key is the owner
itself.  It is deliberately not called a physical mass-read support.

Only finite combinatorics is proved here.  `OPEN_measurability`,
`OPEN_previsibility`, and `OPEN_actualReadSupport` remain model-facing gaps;
no stopping-time, conditional-independence, or Hamiltonian read-support
claim is made.
-/

namespace ArchonPhysics.ActualFPUTR1AtomOnlineOpenCloseProducer

set_option autoImplicit false

open ArchonPhysics
open ArchonPhysics.ActualClusterRawMoleculeKineticPeel
open ArchonPhysics.ActualFPUTAddressedCoupleCommonChronology
open ArchonPhysics.ActualFPUTCompletedCellClassifier
open ArchonPhysics.ActualFPUTOnlineOwnerMultiOpenFirstHitCutGlue
open ArchonPhysics.ActualFPUTQ1GoodPacketReadback
open ArchonPhysics.ActualFPUTR1CompletedWordStructuralProducer
open ArchonPhysics.ActualFPUTR1FineFibreFirstHitReadback
open ArchonPhysics.ActualFPUTR1OnlineCompletedCellTransition
open ArchonPhysics.ActualFPUTR1PositiveRoutingProducer
open ArchonPhysics.ContinuousComplexKernelChronologicalShuffle
open ArchonPhysics.PhyslibFPUTActualMixedTreeRawHistoryTimeVertexAddresses

noncomputable section

variable {N : Nat} [NeZero N]
variable {carrier : ActualFPUTClusterRawCoupleCarrier N}
variable {readback : ActualFPUTR1StrictDependencyReadback carrier}

/-! ## Literal atom events -/

/-- A maximal porous block is the structural owner of each atom event. -/
abbrev ActualFPUTR1AtomOnlineOwner :=
  Finset (ActualFPUTR1Atom carrier)

/-- The generic guard is keyed by the structural owner.  This is only an
open-slot key and is not asserted to be an actual random-mass read support. -/
abbrev ActualFPUTR1AtomOnlineStructuralKey :=
  ActualFPUTR1AtomOnlineOwner (carrier := carrier)

/-- Prefix payload in literal hole-to-root order. -/
abbrev ActualFPUTR1AtomOnlinePayload :=
  List (ActualFPUTR1Atom carrier × ContinuousComplexKernel)

/-- `open` is the first atom seen for an owner, `read` is a later atom, and
`close` is emitted immediately after the read which completes that owner. -/
inductive ActualFPUTR1AtomOnlineEventKind
  | open
  | read
  | close
  deriving DecidableEq, Repr

/-- Exact root-to-hole atom word retained by the indexed R1 fine fibre,
reversed to give the online hole-to-root scan. -/
def actualFPUTR1HoleToRootAtomWord
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    List (ActualFPUTR1Atom carrier) :=
  completed.fine.atomWord.reverse

@[simp] theorem actualFPUTR1HoleToRootAtomWord_length
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    (actualFPUTR1HoleToRootAtomWord completed).length =
      completed.fine.atomWord.length := by
  simp [actualFPUTR1HoleToRootAtomWord]

theorem actualFPUTR1HoleToRootAtomWord_nodup
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    (actualFPUTR1HoleToRootAtomWord completed).Nodup := by
  rw [actualFPUTR1HoleToRootAtomWord, List.nodup_reverse]
  exact completed.fine.atomWord_nodup

/-- Literal atom at one position of the reversed fine word. -/
def actualFPUTR1HoleToRootAtomAt
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    ActualFPUTR1Atom carrier :=
  (actualFPUTR1HoleToRootAtomWord completed).get atomPos

/-- The coefficient-complete owner is decoded from the current atom, not
from the global first-occurrence ordering of completed cells. -/
def actualFPUTR1HoleToRootOwnerAt
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    ActualFPUTR1AtomOnlineOwner (carrier := carrier) :=
  maximalPorousBlock readback.dependency
    (actualFPUTR1HoleToRootAtomAt completed atomPos)

/-- Every decoded owner is literally one maximal dependency component. -/
theorem actualFPUTR1HoleToRootOwnerAt_coefficientComplete
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    IsCoefficientCompleteMacroCell readback.dependency
      (actualFPUTR1HoleToRootOwnerAt completed atomPos) :=
  ⟨actualFPUTR1HoleToRootAtomAt completed atomPos, rfl⟩

/-- Prefix strictly before the current atom. -/
def actualFPUTR1HoleToRootPrefixBefore
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    List (ActualFPUTR1Atom carrier) :=
  (actualFPUTR1HoleToRootAtomWord completed).take atomPos.val

/-- Prefix through and including the current atom. -/
def actualFPUTR1HoleToRootPrefixThrough
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    List (ActualFPUTR1Atom carrier) :=
  (actualFPUTR1HoleToRootAtomWord completed).take (atomPos.val + 1)

/-- Whether this owner already occurred in the strict scan prefix. -/
def actualFPUTR1HoleToRootOwnerSeenBefore
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) : Prop :=
  ∃ earlier ∈ actualFPUTR1HoleToRootPrefixBefore completed atomPos,
    maximalPorousBlock readback.dependency earlier =
      actualFPUTR1HoleToRootOwnerAt completed atomPos

/-- Prefix-only close predicate: after reading the current atom, every atom
of its structural owner has appeared in the scanned prefix. -/
def actualFPUTR1HoleToRootClosesAt
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) : Prop :=
  actualFPUTR1HoleToRootOwnerAt completed atomPos ⊆
    (actualFPUTR1HoleToRootPrefixThrough completed atomPos).toFinset

/-- Kernel decoration inherited from the exact indexed fine fibre. -/
def actualFPUTR1HoleToRootDecorateAtom
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atom : ActualFPUTR1Atom carrier) :
    ActualFPUTR1Atom carrier × ContinuousComplexKernel :=
  (atom, actualFPUTSideTaggedCoupleKernelAt
    completed.fine.leftKernelAt completed.fine.rightKernelAt atom)

/-- Owner payload visible through the current prefix.  No suffix atom is
included in this list. -/
def actualFPUTR1HoleToRootPayloadAt
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    ActualFPUTR1AtomOnlinePayload (carrier := carrier) :=
  (actualFPUTR1HoleToRootPrefixThrough completed atomPos).filter
      (fun atom => atom ∈ actualFPUTR1HoleToRootOwnerAt completed atomPos)
    |>.map (actualFPUTR1HoleToRootDecorateAtom completed)

/-- One fully typed chronology event.  All fields are retained rather than
recovered from a completed-cell scan rank. -/
structure ActualFPUTR1AtomOnlineEvent
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) where
  fineIndex : Fin
    (actualFPUTSideTaggedCommonAddressLinearExtensions
      carrier.leftTree carrier.rightTree).length
  atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length
  kind : ActualFPUTR1AtomOnlineEventKind
  atom : ActualFPUTR1Atom carrier
  owner : ActualFPUTR1AtomOnlineOwner (carrier := carrier)
  payload : ActualFPUTR1AtomOnlinePayload (carrier := carrier)

/-- Canonical event at a fixed atom position and phase. -/
def actualFPUTR1AtomOnlineEventAt
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length)
    (kind : ActualFPUTR1AtomOnlineEventKind) :
    ActualFPUTR1AtomOnlineEvent completed where
  fineIndex := completed.fine.historyIndex
  atomPos := atomPos
  kind := kind
  atom := actualFPUTR1HoleToRootAtomAt completed atomPos
  owner := actualFPUTR1HoleToRootOwnerAt completed atomPos
  payload := actualFPUTR1HoleToRootPayloadAt completed atomPos

/-- One atom always emits an open-or-read event.  If that read completes the
owner using only the prefix-through predicate, a close event follows at the
same literal atom position. -/
def actualFPUTR1AtomOnlineEventsAt
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    List (ActualFPUTR1AtomOnlineEvent completed) := by
  classical
  let firstKind :=
    if actualFPUTR1HoleToRootOwnerSeenBefore completed atomPos then
      ActualFPUTR1AtomOnlineEventKind.read
    else
      ActualFPUTR1AtomOnlineEventKind.open
  exact actualFPUTR1AtomOnlineEventAt completed atomPos firstKind ::
    if actualFPUTR1HoleToRootClosesAt completed atomPos then
      [actualFPUTR1AtomOnlineEventAt completed atomPos .close]
    else []

/-- Finite literal event word.  `List.ofFn` retains every atom position and
`flatten` retains the possible second (close) event at that same position. -/
def actualFPUTR1AtomOnlineEventWord
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    List (ActualFPUTR1AtomOnlineEvent completed) :=
  ((List.ofFn fun atomPos :
      Fin (actualFPUTR1HoleToRootAtomWord completed).length => atomPos).map
        (actualFPUTR1AtomOnlineEventsAt completed)).flatten

@[simp] theorem actualFPUTR1AtomOnlineEventAt_fineIndex
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length)
    (kind : ActualFPUTR1AtomOnlineEventKind) :
    (actualFPUTR1AtomOnlineEventAt completed atomPos kind).fineIndex =
      completed.fine.historyIndex := rfl

@[simp] theorem actualFPUTR1AtomOnlineEventAt_atomPos
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length)
    (kind : ActualFPUTR1AtomOnlineEventKind) :
    (actualFPUTR1AtomOnlineEventAt completed atomPos kind).atomPos = atomPos :=
  rfl

@[simp] theorem actualFPUTR1AtomOnlineEventAt_kind
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length)
    (kind : ActualFPUTR1AtomOnlineEventKind) :
    (actualFPUTR1AtomOnlineEventAt completed atomPos kind).kind = kind := rfl

@[simp] theorem actualFPUTR1AtomOnlineEventAt_owner
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length)
    (kind : ActualFPUTR1AtomOnlineEventKind) :
    (actualFPUTR1AtomOnlineEventAt completed atomPos kind).owner =
      actualFPUTR1HoleToRootOwnerAt completed atomPos := rfl

@[simp] theorem actualFPUTR1AtomOnlineEventAt_payload
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length)
    (kind : ActualFPUTR1AtomOnlineEventKind) :
    (actualFPUTR1AtomOnlineEventAt completed atomPos kind).payload =
      actualFPUTR1HoleToRootPayloadAt completed atomPos := rfl

/-! ## Exact finite rebuild and close uniqueness -/

/-- Project an open/read event to the atom it consumes; close is a second
bookkeeping event at the same atom position and consumes no additional atom. -/
def ActualFPUTR1AtomOnlineEvent.consumedAtom?
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    Option (ActualFPUTR1Atom carrier) :=
  match event.kind with
  | .open | .read => some event.atom
  | .close => none

private theorem filterMap_eventsAt_consumedAtom
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    (actualFPUTR1AtomOnlineEventsAt completed atomPos).filterMap
        ActualFPUTR1AtomOnlineEvent.consumedAtom? =
      [actualFPUTR1HoleToRootAtomAt completed atomPos] := by
  classical
  by_cases hseen :
      actualFPUTR1HoleToRootOwnerSeenBefore completed atomPos <;>
    by_cases hclose : actualFPUTR1HoleToRootClosesAt completed atomPos <;>
    simp [actualFPUTR1AtomOnlineEventsAt, hseen, hclose,
      ActualFPUTR1AtomOnlineEvent.consumedAtom?,
      actualFPUTR1AtomOnlineEventAt, actualFPUTR1HoleToRootAtomAt]

private theorem filterMap_eventBundles_consumedAtom
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (positions :
      List (Fin (actualFPUTR1HoleToRootAtomWord completed).length)) :
    List.filterMap ActualFPUTR1AtomOnlineEvent.consumedAtom?
        ((positions.map
          (actualFPUTR1AtomOnlineEventsAt completed)).flatten) =
      positions.map (actualFPUTR1HoleToRootAtomAt completed) := by
  induction positions with
  | nil => rfl
  | cons atomPos positions induction =>
      simp [filterMap_eventsAt_consumedAtom, induction]

/-- Erasing close bookkeeping and projecting open/read events reconstructs
the exact reversed fine atom word. -/
theorem actualFPUTR1AtomOnlineEventWord_rebuild_atoms
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    (actualFPUTR1AtomOnlineEventWord completed).filterMap
        ActualFPUTR1AtomOnlineEvent.consumedAtom? =
      actualFPUTR1HoleToRootAtomWord completed := by
  classical
  rw [actualFPUTR1AtomOnlineEventWord,
    filterMap_eventBundles_consumedAtom]
  rw [List.map_ofFn]
  simpa [Function.comp_def, actualFPUTR1HoleToRootAtomAt] using
    (List.ofFn_get (actualFPUTR1HoleToRootAtomWord completed))

private theorem get_not_mem_take_succ_of_lt
    {alpha : Type*} (word : List alpha) (hnodup : word.Nodup)
    (left right : Fin word.length) (hlt : left.val < right.val) :
    word.get right ∉ word.take (left.val + 1) := by
  intro hmem
  rcases List.mem_iff_get.mp hmem with ⟨earlier, hearlier⟩
  have hearlierBound :
      earlier.val < Nat.min (left.val + 1) word.length := by
    simpa using earlier.isLt
  have hearlierLtWord : earlier.val < word.length :=
    lt_of_lt_of_le hearlierBound (Nat.min_le_right _ _)
  let earlierFull : Fin word.length := ⟨earlier.val, hearlierLtWord⟩
  have hgetTake :
      (word.take (left.val + 1)).get earlier = word.get earlierFull := by
    change (word.take (left.val + 1))[earlier.val] = word[earlier.val]
    exact List.getElem_take
  have hsame : word.get earlierFull = word.get right :=
    hgetTake.symm.trans hearlier
  have hposition : earlierFull = right :=
    hnodup.get_inj_iff.mp hsame
  have hval : earlier.val = right.val := by
    simpa [earlierFull] using congrArg Fin.val hposition
  have hearlierLe : earlier.val < left.val + 1 :=
    lt_of_lt_of_le hearlierBound (Nat.min_le_left _ _)
  omega

/-- Two prefix-completing positions for the same owner are equal.  Hence a
porous owner has at most one generated close, even when its atoms occur in
an `A-B-A` interleaving. -/
theorem actualFPUTR1HoleToRootClosePosition_unique
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (left right : Fin (actualFPUTR1HoleToRootAtomWord completed).length)
    (hleft : actualFPUTR1HoleToRootClosesAt completed left)
    (hright : actualFPUTR1HoleToRootClosesAt completed right)
    (howner : actualFPUTR1HoleToRootOwnerAt completed left =
      actualFPUTR1HoleToRootOwnerAt completed right) :
    left = right := by
  classical
  apply Fin.eq_of_val_eq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlr | hrl
  · have hrightOwner : actualFPUTR1HoleToRootAtomAt completed right ∈
        actualFPUTR1HoleToRootOwnerAt completed left := by
      rw [howner]
      exact anchor_mem_maximalPorousBlock readback.dependency _
    have hrightPrefixFinset :
        actualFPUTR1HoleToRootAtomAt completed right ∈
          (actualFPUTR1HoleToRootPrefixThrough completed left).toFinset :=
      hleft hrightOwner
    have hrightPrefix :
        actualFPUTR1HoleToRootAtomAt completed right ∈
          actualFPUTR1HoleToRootPrefixThrough completed left := by
      simpa using hrightPrefixFinset
    exact (get_not_mem_take_succ_of_lt
      (actualFPUTR1HoleToRootAtomWord completed)
      (actualFPUTR1HoleToRootAtomWord_nodup completed)
      left right hlr) hrightPrefix
  · have hleftOwner : actualFPUTR1HoleToRootAtomAt completed left ∈
        actualFPUTR1HoleToRootOwnerAt completed right := by
      rw [← howner]
      exact anchor_mem_maximalPorousBlock readback.dependency _
    have hleftPrefixFinset :
        actualFPUTR1HoleToRootAtomAt completed left ∈
          (actualFPUTR1HoleToRootPrefixThrough completed right).toFinset :=
      hright hleftOwner
    have hleftPrefix :
        actualFPUTR1HoleToRootAtomAt completed left ∈
          actualFPUTR1HoleToRootPrefixThrough completed right := by
      simpa using hleftPrefixFinset
    exact (get_not_mem_take_succ_of_lt
      (actualFPUTR1HoleToRootAtomWord completed)
      (actualFPUTR1HoleToRootAtomWord_nodup completed)
      right left hrl) hleftPrefix

@[simp] theorem actualFPUTR1AtomOnlineClose_mem_eventsAt_iff
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    actualFPUTR1AtomOnlineEventAt completed atomPos .close ∈
        actualFPUTR1AtomOnlineEventsAt completed atomPos ↔
      actualFPUTR1HoleToRootClosesAt completed atomPos := by
  classical
  by_cases hseen :
      actualFPUTR1HoleToRootOwnerSeenBefore completed atomPos <;>
    by_cases hclose : actualFPUTR1HoleToRootClosesAt completed atomPos <;>
    simp [actualFPUTR1AtomOnlineEventsAt, hseen, hclose,
      actualFPUTR1AtomOnlineEventAt]

/-- Positions whose current atom has a prescribed structural owner. -/
def actualFPUTR1HoleToRootOwnerPositions
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (owner : ActualFPUTR1AtomOnlineOwner (carrier := carrier)) :
    Finset (Fin (actualFPUTR1HoleToRootAtomWord completed).length) := by
  classical
  exact Finset.univ.filter fun atomPos =>
    actualFPUTR1HoleToRootOwnerAt completed atomPos = owner

@[simp] theorem mem_actualFPUTR1HoleToRootOwnerPositions
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (owner : ActualFPUTR1AtomOnlineOwner (carrier := carrier))
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    atomPos ∈ actualFPUTR1HoleToRootOwnerPositions completed owner ↔
      actualFPUTR1HoleToRootOwnerAt completed atomPos = owner := by
  classical
  simp [actualFPUTR1HoleToRootOwnerPositions]

theorem actualFPUTR1HoleToRootAtom_mem
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atom : ActualFPUTR1Atom carrier) :
    atom ∈ actualFPUTR1HoleToRootAtomWord completed := by
  simpa [actualFPUTR1HoleToRootAtomWord] using
    completed.fine.atomWord_exhaustive atom

theorem actualFPUTR1HoleToRootOwnerPositions_nonempty
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (anchor : ActualFPUTR1Atom carrier) :
    (actualFPUTR1HoleToRootOwnerPositions completed
      (maximalPorousBlock readback.dependency anchor)).Nonempty := by
  classical
  rcases List.mem_iff_get.mp
      (actualFPUTR1HoleToRootAtom_mem completed anchor) with
    ⟨atomPos, hatomPos⟩
  refine ⟨atomPos, ?_⟩
  apply (mem_actualFPUTR1HoleToRootOwnerPositions _ _ _).mpr
  change maximalPorousBlock readback.dependency
      ((actualFPUTR1HoleToRootAtomWord completed).get atomPos) =
    maximalPorousBlock readback.dependency anchor
  rw [hatomPos]

/-- Last literal scan position belonging to the owner of an anchor atom. -/
noncomputable def actualFPUTR1HoleToRootLastOwnerPosition
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (anchor : ActualFPUTR1Atom carrier) :
    Fin (actualFPUTR1HoleToRootAtomWord completed).length :=
  (actualFPUTR1HoleToRootOwnerPositions completed
    (maximalPorousBlock readback.dependency anchor)).max'
      (actualFPUTR1HoleToRootOwnerPositions_nonempty completed anchor)

theorem actualFPUTR1HoleToRootLastOwnerPosition_owner
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (anchor : ActualFPUTR1Atom carrier) :
    actualFPUTR1HoleToRootOwnerAt completed
        (actualFPUTR1HoleToRootLastOwnerPosition completed anchor) =
      maximalPorousBlock readback.dependency anchor := by
  exact (mem_actualFPUTR1HoleToRootOwnerPositions
    completed (maximalPorousBlock readback.dependency anchor)
    (actualFPUTR1HoleToRootLastOwnerPosition completed anchor)).mp
      (Finset.max'_mem _ _)

/-- The last position of an owner's atoms really satisfies the prefix-only
close predicate.  The proof uses exhaustiveness and the maximal-position
property, not the global completed-cell list order. -/
theorem actualFPUTR1HoleToRootLastOwnerPosition_closes
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (anchor : ActualFPUTR1Atom carrier) :
    actualFPUTR1HoleToRootClosesAt completed
      (actualFPUTR1HoleToRootLastOwnerPosition completed anchor) := by
  classical
  intro atom hatom
  have hatomBlock :
      atom ∈ maximalPorousBlock readback.dependency anchor := by
    simpa [actualFPUTR1HoleToRootLastOwnerPosition_owner] using hatom
  rcases List.mem_iff_get.mp
      (actualFPUTR1HoleToRootAtom_mem completed atom) with
    ⟨atomPos, hatomPos⟩
  have hsame :
      InSameMaximalPorousBlock readback.dependency anchor atom :=
    (mem_maximalPorousBlock_iff readback.dependency anchor atom).mp hatomBlock
  have hownerAt :
      actualFPUTR1HoleToRootOwnerAt completed atomPos =
        maximalPorousBlock readback.dependency anchor := by
    unfold actualFPUTR1HoleToRootOwnerAt
      actualFPUTR1HoleToRootAtomAt
    rw [hatomPos]
    exact (maximalPorousBlock_eq_of_sameBlock
      readback.dependency hsame).symm
  have hatomPosMem :
      atomPos ∈ actualFPUTR1HoleToRootOwnerPositions completed
        (maximalPorousBlock readback.dependency anchor) :=
    (mem_actualFPUTR1HoleToRootOwnerPositions _ _ _).mpr hownerAt
  have hle := (actualFPUTR1HoleToRootOwnerPositions completed
    (maximalPorousBlock readback.dependency anchor)).le_max'
      atomPos hatomPosMem
  change atomPos.val ≤
    (actualFPUTR1HoleToRootLastOwnerPosition completed anchor).val at hle
  have hlt : atomPos.val <
      (actualFPUTR1HoleToRootLastOwnerPosition completed anchor).val + 1 :=
    Nat.lt_succ_of_le hle
  have htakeLength : atomPos.val <
      (actualFPUTR1HoleToRootPrefixThrough completed
        (actualFPUTR1HoleToRootLastOwnerPosition completed anchor)).length := by
    simp only [actualFPUTR1HoleToRootPrefixThrough, List.length_take]
    exact lt_min hlt atomPos.isLt
  let prefixPos : Fin
      (actualFPUTR1HoleToRootPrefixThrough completed
        (actualFPUTR1HoleToRootLastOwnerPosition completed anchor)).length :=
    ⟨atomPos.val, htakeLength⟩
  have hget :
      (actualFPUTR1HoleToRootPrefixThrough completed
        (actualFPUTR1HoleToRootLastOwnerPosition completed anchor)).get
          prefixPos = atom := by
    calc
      _ = (actualFPUTR1HoleToRootAtomWord completed).get atomPos := by
        simpa [prefixPos, actualFPUTR1HoleToRootPrefixThrough] using
          (List.getElem_take' atomPos.isLt hlt).symm
      _ = atom := hatomPos
  simpa using (List.mem_iff_get.mpr ⟨prefixPos, hget⟩)

/-- Every actual maximal owner emits exactly one close event. -/
theorem actualFPUTR1AtomOnline_existsUnique_close_of_anchor
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (anchor : ActualFPUTR1Atom carrier) :
    ∃! atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length,
      actualFPUTR1AtomOnlineEventAt completed atomPos .close ∈
          actualFPUTR1AtomOnlineEventsAt completed atomPos ∧
        (actualFPUTR1AtomOnlineEventAt completed atomPos .close).owner =
          maximalPorousBlock readback.dependency anchor := by
  let lastPos := actualFPUTR1HoleToRootLastOwnerPosition completed anchor
  refine ⟨lastPos, ?_, ?_⟩
  · constructor
    · exact (actualFPUTR1AtomOnlineClose_mem_eventsAt_iff
        completed lastPos).mpr
          (actualFPUTR1HoleToRootLastOwnerPosition_closes completed anchor)
    · exact actualFPUTR1HoleToRootLastOwnerPosition_owner completed anchor
  · intro other hother
    apply actualFPUTR1HoleToRootClosePosition_unique completed other lastPos
    · exact (actualFPUTR1AtomOnlineClose_mem_eventsAt_iff
        completed other).mp hother.1
    · exact actualFPUTR1HoleToRootLastOwnerPosition_closes completed anchor
    · exact hother.2.trans
        (actualFPUTR1HoleToRootLastOwnerPosition_owner
          completed anchor).symm

/-- In particular every certified completed-cell owner has exactly one close
in the atom-level event stream. -/
theorem actualFPUTR1AtomOnline_existsUnique_close_of_completedCell
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (cellIndex : Fin completed.word.cells.length) :
    ∃! atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length,
      actualFPUTR1AtomOnlineEventAt completed atomPos .close ∈
          actualFPUTR1AtomOnlineEventsAt completed atomPos ∧
        (actualFPUTR1AtomOnlineEventAt completed atomPos .close).owner =
          completed.word.cells.get cellIndex := by
  rcases completed.word.cell_complete cellIndex with ⟨anchor, hcell⟩
  rw [hcell]
  exact actualFPUTR1AtomOnline_existsUnique_close_of_anchor completed anchor

/-! ## Generic keyed multi-open classifier -/

/-- Open and read events propose `ret`; close events use the existing actual
strict packet route on the complete structural owner. -/
noncomputable def actualFPUTR1AtomOnlinePropose
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (_state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    ActualFPUTOnlineMultiOpenTransition
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)) :=
  match event.kind with
  | .open | .read => .ret event.owner event.owner event.payload
  | .close =>
      match actualFPUTR1StrictPacketRoute readback
          (positiveRetainAdmissible semantics) event.owner with
      | .pmem _ => .pmem event.owner event.owner event.payload
      | .strictDirichletGood _ _ =>
          .freshHit event.owner event.owner event.payload
      | .routedComplement _ _ => .bad event.owner event.owner event.payload

/-- Actual atom-event instance of the generic multi-open classifier. -/
noncomputable def actualFPUTR1AtomOnlineMachine
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    ActualFPUTOnlineMultiOpenMachine
      (ActualFPUTR1AtomOnlineEvent completed)
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)) where
  propose := actualFPUTR1AtomOnlinePropose semantics completed

@[simp] theorem actualFPUTR1AtomOnlinePropose_owner
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    ((actualFPUTR1AtomOnlineMachine semantics completed).propose
      state event).owner = event.owner := by
  change (actualFPUTR1AtomOnlinePropose semantics completed state event).owner =
    event.owner
  unfold actualFPUTR1AtomOnlinePropose
  split <;> try rfl
  all_goals split <;> rfl

/-- At a generated close, the actual proposal class is exactly the existing
strict completed-block sector.  Only the structural key differs from the
completed-cell adapter; it makes no physical read-support assertion. -/
theorem actualFPUTR1AtomOnline_closeProposedClass_eq_sector
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (event : ActualFPUTR1AtomOnlineEvent completed)
    (hclose : event.kind = .close) :
    actualFPUTR1OnlineCompletedCellTransitionClass
        ((actualFPUTR1AtomOnlineMachine semantics completed).propose
          state event) =
      actualFPUTR1OnlineCompletedCellClassOfSector
        (completedCellSector (positiveRoutingSpec semantics) event.owner) := by
  by_cases hret : positiveRetainAdmissible semantics event.owner
  · simp [actualFPUTR1AtomOnlineMachine, actualFPUTR1AtomOnlinePropose,
      hclose, actualFPUTR1StrictPacketRoute, completedCellSector,
      positiveRoutingSpec, actualFPUTR1StrictRoutingSpec, hret,
      actualFPUTR1OnlineCompletedCellTransitionClass,
      actualFPUTR1OnlineCompletedCellClassOfSector]
  · by_cases hgood : Nonempty
      (ActualFPUTR1StrictDirichletGoodPacketCertificate readback event.owner)
    · simp [actualFPUTR1AtomOnlineMachine, actualFPUTR1AtomOnlinePropose,
        hclose, actualFPUTR1StrictPacketRoute, completedCellSector,
        positiveRoutingSpec, actualFPUTR1StrictRoutingSpec, hret, hgood,
        actualFPUTR1OnlineCompletedCellTransitionClass,
        actualFPUTR1OnlineCompletedCellClassOfSector]
    · simp [actualFPUTR1AtomOnlineMachine, actualFPUTR1AtomOnlinePropose,
        hclose, actualFPUTR1StrictPacketRoute, completedCellSector,
        positiveRoutingSpec, actualFPUTR1StrictRoutingSpec, hret, hgood,
        actualFPUTR1OnlineCompletedCellTransitionClass,
        actualFPUTR1OnlineCompletedCellClassOfSector]

@[simp] theorem actualFPUTR1AtomOnlinePropose_payKey
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    ((actualFPUTR1AtomOnlineMachine semantics completed).propose
      state event).payKey = event.owner := by
  change
    (actualFPUTR1AtomOnlinePropose semantics completed state event).payKey =
      event.owner
  unfold actualFPUTR1AtomOnlinePropose
  split <;> try rfl
  all_goals split <;> rfl

@[simp] theorem actualFPUTR1AtomOnlinePropose_payload
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    ((actualFPUTR1AtomOnlineMachine semantics completed).propose
      state event).payload = event.payload := by
  change
    (actualFPUTR1AtomOnlinePropose semantics completed state event).payload =
      event.payload
  unfold actualFPUTR1AtomOnlinePropose
  split <;> try rfl
  all_goals split <;> rfl

/-- Reachable structural-key states never reserve a key for another owner. -/
def ActualFPUTR1AtomOnlineState.IsStructurallyKeyed
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier))) : Prop :=
  ∀ key, state.reservedOwner key = none ∨
    state.reservedOwner key = some key

theorem actualFPUTR1AtomOnline_empty_isStructurallyKeyed :
    ActualFPUTR1AtomOnlineState.IsStructurallyKeyed
      (ActualFPUTOnlineMultiOpenState.empty :
        ActualFPUTOnlineMultiOpenState
          (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
          (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
          (ActualFPUTR1AtomOnlinePayload (carrier := carrier))) := by
  intro key
  exact Or.inl rfl

private theorem actualFPUTR1AtomOnline_structurallyKeyed_update_self
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (hstate : ActualFPUTR1AtomOnlineState.IsStructurallyKeyed state)
    (owner : ActualFPUTR1AtomOnlineOwner (carrier := carrier)) :
    ActualFPUTR1AtomOnlineState.IsStructurallyKeyed
      { state with
        reservedOwner :=
          Function.update state.reservedOwner owner (some owner) } := by
  intro key
  by_cases hkey : key = owner
  · subst key
    exact Or.inr (by simp [Function.update])
  · simpa [Function.update, hkey] using hstate key

/-- Any generic transition whose owner equals its structural key preserves
the keyed-reservation invariant.  A bad transition preserves it because the
generic machine leaves the state unchanged. -/
theorem actualFPUTR1AtomOnline_apply_preserves_structurallyKeyed
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (hstate : ActualFPUTR1AtomOnlineState.IsStructurallyKeyed state)
    (transition : ActualFPUTOnlineMultiOpenTransition
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (hkey : transition.owner = transition.payKey) :
    ActualFPUTR1AtomOnlineState.IsStructurallyKeyed
      (applyActualFPUTOnlineMultiOpenTransition state transition) := by
  cases transition with
  | ret owner payKey payload =>
      change owner = payKey at hkey
      subst payKey
      exact actualFPUTR1AtomOnline_structurallyKeyed_update_self
        state hstate owner
  | pmem owner payKey payload =>
      change owner = payKey at hkey
      subst payKey
      exact actualFPUTR1AtomOnline_structurallyKeyed_update_self
        state hstate owner
  | freshHit owner payKey payload =>
      change owner = payKey at hkey
      subst payKey
      exact actualFPUTR1AtomOnline_structurallyKeyed_update_self
        state hstate owner
  | bad owner payKey payload =>
      exact hstate

theorem actualFPUTR1AtomOnline_ownerReadAllowed_of_structurallyKeyed
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (hstate : ActualFPUTR1AtomOnlineState.IsStructurallyKeyed state)
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    state.IsOwnerReadAllowed
      ((actualFPUTR1AtomOnlineMachine semantics completed).propose
        state event).owner
      ((actualFPUTR1AtomOnlineMachine semantics completed).propose
        state event).payKey := by
  rw [actualFPUTR1AtomOnlinePropose_owner,
    actualFPUTR1AtomOnlinePropose_payKey]
  exact hstate event.owner

/-- On every structurally keyed prefix state the generic guard leaves the
actual atom proposal unchanged. -/
theorem actualFPUTR1AtomOnline_classify_eq_propose_of_structurallyKeyed
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (hstate : ActualFPUTR1AtomOnlineState.IsStructurallyKeyed state)
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    (actualFPUTR1AtomOnlineMachine semantics completed).classify state event =
      (actualFPUTR1AtomOnlineMachine semantics completed).propose state event :=
  by
    exact ActualFPUTOnlineMultiOpenMachine.classify_eq_propose_of_allowed
      (actualFPUTR1AtomOnlineMachine semantics completed) state event
        (actualFPUTR1AtomOnline_ownerReadAllowed_of_structurallyKeyed
          semantics completed state hstate event)

/-- One live atom step preserves the keyed invariant; after a fresh hit the
generic freeze preserves it trivially. -/
theorem actualFPUTR1AtomOnline_step_preserves_structurallyKeyed
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (hstate : ActualFPUTR1AtomOnlineState.IsStructurallyKeyed state)
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    ActualFPUTR1AtomOnlineState.IsStructurallyKeyed
      ((actualFPUTR1AtomOnlineMachine semantics completed).step state event) := by
  by_cases hhit : state.hitFlag = true
  · rw [(actualFPUTR1AtomOnlineMachine semantics completed).step_of_hitFlag_true
      state event hhit]
    exact hstate
  · rw [ActualFPUTOnlineMultiOpenMachine.step]
    simp only [hhit]
    rw [actualFPUTR1AtomOnline_classify_eq_propose_of_structurallyKeyed
      semantics completed state hstate event]
    apply actualFPUTR1AtomOnline_apply_preserves_structurallyKeyed state hstate
    rw [actualFPUTR1AtomOnlinePropose_owner,
      actualFPUTR1AtomOnlinePropose_payKey]

/-- Every finite event prefix reached from a keyed state remains keyed. -/
theorem actualFPUTR1AtomOnline_foldl_preserves_structurallyKeyed
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (events : List (ActualFPUTR1AtomOnlineEvent completed))
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (hstate : ActualFPUTR1AtomOnlineState.IsStructurallyKeyed state) :
    ActualFPUTR1AtomOnlineState.IsStructurallyKeyed
      (events.foldl
        (actualFPUTR1AtomOnlineMachine semantics completed).step state) := by
  induction events generalizing state with
  | nil => exact hstate
  | cons event events induction =>
      exact induction
        ((actualFPUTR1AtomOnlineMachine semantics completed).step state event)
        (actualFPUTR1AtomOnline_step_preserves_structurallyKeyed
          semantics completed state hstate event)

/-- Therefore the generic guard leaves the proposal unchanged after every
actual atom-event prefix, including interleaved prefixes. -/
theorem actualFPUTR1AtomOnline_classify_after_prefix_eq_propose
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (scannedPrefix : List (ActualFPUTR1AtomOnlineEvent completed))
    (event : ActualFPUTR1AtomOnlineEvent completed) :
    let state := scannedPrefix.foldl
      (actualFPUTR1AtomOnlineMachine semantics completed).step
      (ActualFPUTOnlineMultiOpenState.empty :
        ActualFPUTOnlineMultiOpenState
          (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
          (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
          (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (actualFPUTR1AtomOnlineMachine semantics completed).classify state event =
      (actualFPUTR1AtomOnlineMachine semantics completed).propose
        state event := by
  dsimp only
  apply actualFPUTR1AtomOnline_classify_eq_propose_of_structurallyKeyed
  exact actualFPUTR1AtomOnline_foldl_preserves_structurallyKeyed
    semantics completed scannedPrefix _
      actualFPUTR1AtomOnline_empty_isStructurallyKeyed

/-- The generic finite trace preserves the complete typed event word. -/
@[simp] theorem actualFPUTR1AtomOnline_trace_rebuild
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    ((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).map
        (fun entry => entry.occurrence) =
      actualFPUTR1AtomOnlineEventWord completed :=
  (actualFPUTR1AtomOnlineMachine semantics completed).trace_map_occurrence _

/-- The generic first-live-hit Cut/Glue rebuild specializes verbatim to the
atom event word; the selected occurrence still contains fineIndex/atomPos,
owner, and prefix payload. -/
theorem actualFPUTR1AtomOnline_firstFreshHit_rebuild
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (hit : ActualFPUTOnlineMultiOpenFirstFreshHit
      (actualFPUTR1AtomOnlineMachine semantics completed)
      (actualFPUTR1AtomOnlineEventWord completed)) :
    hit.fibreKey.regularPrefix ++ [hit.fibreKey.selected] ++ hit.suffix =
      actualFPUTR1AtomOnlineEventWord completed :=
  hit.rebuild

/-! ## Typed A-B-A sanity theorem -/

/-- Opening `A`, then `B`, then reading `A` updates only `A`'s pending
payload and leaves `B` open.  Reservations also remain owner-keyed.  This is
the finite state fact which a single global completed-cell cursor cannot
represent. -/
theorem actualFPUTR1AtomOnline_keyedState_handles_ABA
    (ownerA ownerB : ActualFPUTR1AtomOnlineOwner (carrier := carrier))
    (hAB : ownerA ≠ ownerB)
    (payloadAOpen payloadBOpen payloadARead :
      ActualFPUTR1AtomOnlinePayload (carrier := carrier)) :
    let emptyState : ActualFPUTOnlineMultiOpenState
        (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
        (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
        (ActualFPUTR1AtomOnlinePayload (carrier := carrier)) := .empty
    let afterAOpen := applyActualFPUTOnlineMultiOpenTransition emptyState
      (.ret ownerA ownerA payloadAOpen)
    let afterBOpen := applyActualFPUTOnlineMultiOpenTransition afterAOpen
      (.ret ownerB ownerB payloadBOpen)
    let afterARead := applyActualFPUTOnlineMultiOpenTransition afterBOpen
      (.ret ownerA ownerA payloadARead)
    afterARead.pending ownerA = some payloadARead ∧
      afterARead.pending ownerB = some payloadBOpen ∧
      afterARead.reservedOwner ownerA = some ownerA ∧
      afterARead.reservedOwner ownerB = some ownerB := by
  dsimp
  simp [applyActualFPUTOnlineMultiOpenTransition, Function.update,
    Ne.symm hAB]

/-!
## Explicitly OPEN model-facing obligations

* `OPEN_measurability`: no event, prefix state, or first-hit map is proved
  measurable.
* `OPEN_previsibility`: reversing and finitely decoding an indexed history is
  not identified with a filtration-previsible physical reveal process.
* `OPEN_actualReadSupport`: the structural owner key is not identified with
  the actual set of masses read by the Hamiltonian coefficient.

Consequently the finite first-live-hit value above is not advertised as a
stopping time.
-/

end

end ArchonPhysics.ActualFPUTR1AtomOnlineOpenCloseProducer
