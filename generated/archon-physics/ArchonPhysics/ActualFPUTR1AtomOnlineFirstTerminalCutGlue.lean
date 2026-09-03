import ArchonPhysics.ActualFPUTR1AtomOnlineOpenCloseProducer
import ArchonPhysics.ActualFPUTFirstIrreducibleDefectClosure

/-!
# First terminal Cut/Glue for the actual R1 atom chronology

The generic multi-open `FirstFreshHit` predicate does not regard `bad` as a
terminal event.  It is therefore not the exact first non-`pmem` cut when a
bad completed owner occurs before the first good owner.

This companion keeps the literal hole-to-root atom trace from
`ActualFPUTR1AtomOnlineOpenCloseProducer`, but declares both live
`freshHit` and live `bad` transitions terminal.  The least terminal trace
position is canonical.  Every earlier live transition is `ret` or `pmem`.
The selected occurrence is a close and its completed-owner sector is either
the strict-good (`firstSeparatedQ1`) sector or `bad`.

No comparison is made between the selected trace index and a completed-cell
list index: the completed word uses first-occurrence deduplication in the
root-to-hole word, while closes occur in literal hole-to-root completion
order.  The bridge below identifies only the owner and its sector.
-/

namespace ArchonPhysics.ActualFPUTR1AtomOnlineFirstTerminalCutGlue

set_option autoImplicit false

open ArchonPhysics
open ArchonPhysics.ActualClusterRawMoleculeKineticPeel
open ArchonPhysics.ActualClusterAllOrderStructuralRecursion
open ArchonPhysics.ActualFPUTCompletedCellClassifier
open ArchonPhysics.ActualFPUTFirstIrreducibleDefectClosure
open ArchonPhysics.ActualFPUTOnlineOwnerMultiOpenFirstHitCutGlue
open ArchonPhysics.ActualFPUTQ1GoodPacketReadback
open ArchonPhysics.ActualFPUTR1AtomOnlineOpenCloseProducer
open ArchonPhysics.ActualFPUTR1CompletedWordStructuralProducer
open ArchonPhysics.ActualFPUTR1FineFibreFirstHitReadback
open ArchonPhysics.ActualFPUTR1OnlineCompletedCellTransition
open ArchonPhysics.ActualFPUTR1PositiveRoutingProducer

noncomputable section

variable {N : Nat} [NeZero N]
variable {carrier : ActualFPUTClusterRawCoupleCarrier N}
variable {readback : ActualFPUTR1StrictDependencyReadback carrier}

/-! ## Generic live terminal predicate -/

/-- A live generic trace entry classified as `bad`. -/
def actualFPUTOnlineMultiOpenTraceEntryIsBad
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    {machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload}
    (entry : ActualFPUTOnlineMultiOpenTraceEntry machine) : Prop :=
  ∃ owner payKey payload,
    entry.transition = some (.bad owner payKey payload)

/-- Exact terminal predicate: a live `freshHit` or a live `bad`. -/
def actualFPUTOnlineMultiOpenTraceEntryIsTerminal
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    {machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload}
    (entry : ActualFPUTOnlineMultiOpenTraceEntry machine) : Prop :=
  entry.IsFreshHit ∨ actualFPUTOnlineMultiOpenTraceEntryIsBad entry

/-- The two nonterminal live routes. -/
def actualFPUTOnlineMultiOpenTraceEntryIsRetOrPmem
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    {machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload}
    (entry : ActualFPUTOnlineMultiOpenTraceEntry machine) : Prop :=
  (∃ owner payKey payload,
      entry.transition = some (.ret owner payKey payload)) ∨
    ∃ owner payKey payload,
      entry.transition = some (.pmem owner payKey payload)

theorem actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    {machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload}
    (entry : ActualFPUTOnlineMultiOpenTraceEntry machine)
    {transition :
      ActualFPUTOnlineMultiOpenTransition Owner PayKey Payload}
    (htransition : entry.transition = some transition) :
    entry.stateBefore.hitFlag = false ∧
      machine.classify entry.stateBefore entry.occurrence = transition := by
  cases hflag : entry.stateBefore.hitFlag with
  | false =>
      have hsome :
          some (machine.classify entry.stateBefore entry.occurrence) =
            some transition := by
        calc
          some (machine.classify entry.stateBefore entry.occurrence) =
              entry.transition := by
            simpa [hflag] using entry.transition_spec.symm
          _ = some transition := htransition
      exact ⟨rfl, Option.some.inj hsome⟩
  | true =>
      have himpossible :
          (none : Option
            (ActualFPUTOnlineMultiOpenTransition Owner PayKey Payload)) =
            some transition := by
        calc
          none = entry.transition := by
            simpa [hflag] using entry.transition_spec.symm
          _ = some transition := htransition
      cases himpossible

theorem actualFPUTOnlineMultiOpenTraceEntry_isRetOrPmem_of_regular_live
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    {machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload}
    (entry : ActualFPUTOnlineMultiOpenTraceEntry machine)
    (hregular :
      ¬ actualFPUTOnlineMultiOpenTraceEntryIsTerminal entry)
    (hlive : entry.transition ≠ none) :
    actualFPUTOnlineMultiOpenTraceEntryIsRetOrPmem entry := by
  cases htransition : entry.transition with
  | none => exact False.elim (hlive htransition)
  | some transition =>
      cases transition with
      | ret owner payKey payload =>
          exact Or.inl ⟨owner, payKey, payload, htransition⟩
      | pmem owner payKey payload =>
          exact Or.inr ⟨owner, payKey, payload, htransition⟩
      | freshHit owner payKey payload =>
          exact False.elim (hregular
            (Or.inl ⟨owner, payKey, payload, htransition⟩))
      | bad owner payKey payload =>
          exact False.elim (hregular
            (Or.inr ⟨owner, payKey, payload, htransition⟩))

private theorem traceFrom_forall_transition_none_of_hitFlag_true
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    (machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload)
    (state : ActualFPUTOnlineMultiOpenState Owner PayKey Payload)
    (word : List Occurrence)
    (hstate : state.hitFlag = true) :
    ∀ entry ∈ machine.traceFrom state word, entry.transition = none := by
  induction word generalizing state with
  | nil =>
      intro entry hentry
      simp [ActualFPUTOnlineMultiOpenMachine.traceFrom] at hentry
  | cons occurrence suffix induction =>
      intro entry hentry
      simp only [ActualFPUTOnlineMultiOpenMachine.traceFrom,
        List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · simp [hstate]
      · rw [machine.step_of_hitFlag_true state occurrence hstate] at hentry
        exact induction state hstate entry hentry

/-- Once a generic trace contains a frozen `none`, every later transition is
also `none`. -/
theorem actualFPUTOnlineMultiOpenTraceFrom_transition_none_pairwise
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    (machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload)
    (state : ActualFPUTOnlineMultiOpenState Owner PayKey Payload)
    (word : List Occurrence) :
    (machine.traceFrom state word).Pairwise fun earlier later =>
      earlier.transition = none → later.transition = none := by
  induction word generalizing state with
  | nil => simp [ActualFPUTOnlineMultiOpenMachine.traceFrom]
  | cons occurrence suffix induction =>
      rw [ActualFPUTOnlineMultiOpenMachine.traceFrom]
      constructor
      · intro later hlater hhead
        have hstate : state.hitFlag = true := by
          by_contra hnot
          simp [hnot] at hhead
        rw [machine.step_of_hitFlag_true state occurrence hstate] at hlater
        exact traceFrom_forall_transition_none_of_hitFlag_true
          machine state suffix hstate later hlater
      · exact induction (machine.step state occurrence)

theorem actualFPUTOnlineMultiOpenTrace_transition_none_pairwise
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    (machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload)
    (word : List Occurrence) :
    (machine.trace word).Pairwise fun earlier later =>
      earlier.transition = none → later.transition = none := by
  exact actualFPUTOnlineMultiOpenTraceFrom_transition_none_pairwise
    machine .empty word

/-! ## Canonical first terminal -/

/-- A least live terminal in the literal atom-event trace.  The disjunction
stores the exact selected route, including its owner, key, and payload. -/
structure ActualFPUTR1AtomOnlineFirstTerminal
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) where
  position : ActualAllOrderFirstDefectPosition
    ((actualFPUTR1AtomOnlineMachine semantics completed).trace
      (actualFPUTR1AtomOnlineEventWord completed))
    actualFPUTOnlineMultiOpenTraceEntryIsTerminal
  owner : ActualFPUTR1AtomOnlineOwner (carrier := carrier)
  payKey : ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier)
  terminalPayload : ActualFPUTR1AtomOnlinePayload (carrier := carrier)
  transition_eq :
    (((actualFPUTR1AtomOnlineMachine semantics completed).trace
      (actualFPUTR1AtomOnlineEventWord completed)).get
        position.index).transition =
          some (.freshHit owner payKey terminalPayload) ∨
    (((actualFPUTR1AtomOnlineMachine semantics completed).trace
      (actualFPUTR1AtomOnlineEventWord completed)).get
        position.index).transition =
          some (.bad owner payKey terminalPayload)

def ActualFPUTR1AtomOnlineFirstTerminal.entry
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    ActualFPUTOnlineMultiOpenTraceEntry
      (actualFPUTR1AtomOnlineMachine semantics completed) :=
  ((actualFPUTR1AtomOnlineMachine semantics completed).trace
    (actualFPUTR1AtomOnlineEventWord completed)).get terminal.position.index

def ActualFPUTR1AtomOnlineFirstTerminal.regularPrefix
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    List (ActualFPUTR1AtomOnlineEvent completed) :=
  terminal.position.regularPrefix.map fun entry => entry.occurrence

def ActualFPUTR1AtomOnlineFirstTerminal.suffix
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    List (ActualFPUTR1AtomOnlineEvent completed) :=
  terminal.position.suffix.map fun entry => entry.occurrence

def ActualFPUTR1AtomOnlineFirstTerminal.fibreKey
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    ActualFPUTOnlineFibreKey (ActualFPUTR1AtomOnlineEvent completed) where
  regularPrefix := terminal.regularPrefix
  selected := terminal.entry.occurrence

theorem ActualFPUTR1AtomOnlineFirstTerminal.rebuild
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    terminal.fibreKey.regularPrefix ++ [terminal.fibreKey.selected] ++
        terminal.suffix = actualFPUTR1AtomOnlineEventWord completed := by
  let project : ActualFPUTOnlineMultiOpenTraceEntry
      (actualFPUTR1AtomOnlineMachine semantics completed) →
        ActualFPUTR1AtomOnlineEvent completed := fun entry => entry.occurrence
  have hrebuild := terminal.position.regularPrefix_cons_suffix
  have hmapped := congrArg (List.map project) hrebuild
  simpa [ActualFPUTR1AtomOnlineFirstTerminal.fibreKey,
    ActualFPUTR1AtomOnlineFirstTerminal.regularPrefix,
    ActualFPUTR1AtomOnlineFirstTerminal.suffix,
    ActualFPUTR1AtomOnlineFirstTerminal.entry, project] using hmapped

theorem actualFPUTR1AtomOnlineFirstTerminal_index_unique
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (left right : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    left.position.index = right.position.index :=
  actualAllOrderFirstDefectPosition_index_unique left.position right.position

theorem ActualFPUTR1AtomOnlineFirstTerminal.selected_isTerminal
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    actualFPUTOnlineMultiOpenTraceEntryIsTerminal terminal.entry :=
  terminal.position.defective

theorem ActualFPUTR1AtomOnlineFirstTerminal.selected_transition_ne_none
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    terminal.entry.transition ≠ none := by
  unfold ActualFPUTR1AtomOnlineFirstTerminal.entry
  rcases terminal.transition_eq with hfresh | hbad
  · rw [hfresh]
    exact Option.some_ne_none _
  · rw [hbad]
    exact Option.some_ne_none _

/-- Every entry strictly before the selected terminal is genuinely live and
is classified `ret` or `pmem`; an earlier `bad` cannot be skipped. -/
theorem ActualFPUTR1AtomOnlineFirstTerminal.earlier_isRetOrPmem
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed)
    (earlier : Fin
      ((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).length)
    (hearlier : earlier.1 < terminal.position.index.1) :
    actualFPUTOnlineMultiOpenTraceEntryIsRetOrPmem
      (((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).get earlier) := by
  let trace := (actualFPUTR1AtomOnlineMachine semantics completed).trace
    (actualFPUTR1AtomOnlineEventWord completed)
  have hregular : ¬ actualFPUTOnlineMultiOpenTraceEntryIsTerminal
      (trace.get earlier) := terminal.position.prefixRegular earlier hearlier
  have hpairwise := actualFPUTOnlineMultiOpenTrace_transition_none_pairwise
    (actualFPUTR1AtomOnlineMachine semantics completed)
    (actualFPUTR1AtomOnlineEventWord completed)
  have hlive : (trace.get earlier).transition ≠ none := by
    intro hnone
    have hselectedNone : (trace.get terminal.position.index).transition = none :=
      hpairwise.rel_get_of_lt (show earlier < terminal.position.index from hearlier)
        hnone
    exact terminal.selected_transition_ne_none hselectedNone
  exact actualFPUTOnlineMultiOpenTraceEntry_isRetOrPmem_of_regular_live
    (trace.get earlier) hregular hlive

def actualFPUTR1AtomOnlineTraceHasTerminal
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) : Prop :=
  ∃ index : Fin
      ((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).length,
    actualFPUTOnlineMultiOpenTraceEntryIsTerminal
      (((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).get index)

theorem nonempty_actualFPUTR1AtomOnlineFirstTerminal_of_hasTerminal
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (hterminal :
      actualFPUTR1AtomOnlineTraceHasTerminal semantics completed) :
    Nonempty (ActualFPUTR1AtomOnlineFirstTerminal semantics completed) := by
  let trace := (actualFPUTR1AtomOnlineMachine semantics completed).trace
    (actualFPUTR1AtomOnlineEventWord completed)
  have hposition : Nonempty (ActualAllOrderFirstDefectPosition trace
      actualFPUTOnlineMultiOpenTraceEntryIsTerminal) :=
    nonempty_firstDefectPosition_of_exists hterminal
  rcases hposition with ⟨position⟩
  rcases position.defective with
    ⟨owner, payKey, payload, hfresh⟩ |
      ⟨owner, payKey, payload, hbad⟩
  · exact ⟨
      { position := position
        owner := owner
        payKey := payKey
        terminalPayload := payload
        transition_eq := Or.inl hfresh }⟩
  · exact ⟨
      { position := position
        owner := owner
        payKey := payKey
        terminalPayload := payload
        transition_eq := Or.inr hbad }⟩

noncomputable def actualFPUTR1AtomOnlineFirstTerminalOfHasTerminal
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (hterminal :
      actualFPUTR1AtomOnlineTraceHasTerminal semantics completed) :
    ActualFPUTR1AtomOnlineFirstTerminal semantics completed :=
  Classical.choice
    (nonempty_actualFPUTR1AtomOnlineFirstTerminal_of_hasTerminal
      semantics completed hterminal)

def ActualFPUTR1AtomOnlineFirstTerminal.cutDatum
    {Index : Type*}
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed)
    (originalIndex : Index) :
    ActualFPUTOnlineCutDatum Index
      (ActualFPUTR1AtomOnlineEvent completed)
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier)) where
  fibreKey := terminal.fibreKey
  owner := terminal.owner
  payKey := terminal.payKey
  originalIndex := originalIndex
  occurrence := terminal.entry.occurrence
  occurrence_eq_selected := rfl

@[simp] theorem ActualFPUTR1AtomOnlineFirstTerminal.glue_cutDatum
    {Index : Type*}
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed)
    (originalIndex : Index) :
    (terminal.cutDatum originalIndex).glue = terminal.entry.occurrence := rfl

theorem ActualFPUTR1AtomOnlineFirstTerminal.cutDatum_rebuild
    {Index : Type*}
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed)
    (originalIndex : Index) :
    (terminal.cutDatum originalIndex).fibreKey.regularPrefix ++
        [(terminal.cutDatum originalIndex).glue] ++ terminal.suffix =
      actualFPUTR1AtomOnlineEventWord completed := by
  simpa [ActualFPUTR1AtomOnlineFirstTerminal.cutDatum,
    ActualFPUTOnlineCutDatum.glue,
    ActualFPUTR1AtomOnlineFirstTerminal.fibreKey] using terminal.rebuild

/-! ## Actual reachable-state and selected-sector facts -/

private theorem actualFPUTR1AtomOnline_traceFrom_entry_structurallyKeyed
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (state : ActualFPUTOnlineMultiOpenState
      (ActualFPUTR1AtomOnlineOwner (carrier := carrier))
      (ActualFPUTR1AtomOnlineStructuralKey (carrier := carrier))
      (ActualFPUTR1AtomOnlinePayload (carrier := carrier)))
    (hstate : ActualFPUTR1AtomOnlineState.IsStructurallyKeyed state)
    (events : List (ActualFPUTR1AtomOnlineEvent completed))
    (entry : ActualFPUTOnlineMultiOpenTraceEntry
      (actualFPUTR1AtomOnlineMachine semantics completed))
    (hentry : entry ∈
      (actualFPUTR1AtomOnlineMachine semantics completed).traceFrom
        state events) :
    ActualFPUTR1AtomOnlineState.IsStructurallyKeyed entry.stateBefore := by
  induction events generalizing state with
  | nil =>
      simp [ActualFPUTOnlineMultiOpenMachine.traceFrom] at hentry
  | cons event suffix induction =>
      simp only [ActualFPUTOnlineMultiOpenMachine.traceFrom,
        List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · exact hstate
      · exact induction
          ((actualFPUTR1AtomOnlineMachine semantics completed).step state event)
          (actualFPUTR1AtomOnline_step_preserves_structurallyKeyed
            semantics completed state hstate event) hentry

theorem actualFPUTR1AtomOnline_trace_entry_structurallyKeyed
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (entry : ActualFPUTOnlineMultiOpenTraceEntry
      (actualFPUTR1AtomOnlineMachine semantics completed))
    (hentry : entry ∈
      (actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)) :
    ActualFPUTR1AtomOnlineState.IsStructurallyKeyed entry.stateBefore := by
  exact actualFPUTR1AtomOnline_traceFrom_entry_structurallyKeyed
    semantics completed .empty actualFPUTR1AtomOnline_empty_isStructurallyKeyed
      (actualFPUTR1AtomOnlineEventWord completed) entry hentry

theorem actualFPUTR1AtomOnline_trace_entry_classify_eq_propose
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (entry : ActualFPUTOnlineMultiOpenTraceEntry
      (actualFPUTR1AtomOnlineMachine semantics completed))
    (hentry : entry ∈
      (actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)) :
    (actualFPUTR1AtomOnlineMachine semantics completed).classify
        entry.stateBefore entry.occurrence =
      (actualFPUTR1AtomOnlineMachine semantics completed).propose
        entry.stateBefore entry.occurrence := by
  exact actualFPUTR1AtomOnline_classify_eq_propose_of_structurallyKeyed
    semantics completed entry.stateBefore
      (actualFPUTR1AtomOnline_trace_entry_structurallyKeyed
        semantics completed entry hentry) entry.occurrence

theorem ActualFPUTR1AtomOnlineFirstTerminal.stateBefore_hitFlag_eq_false
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    terminal.entry.stateBefore.hitFlag = false := by
  rcases terminal.transition_eq with hfresh | hbad
  · exact
      (actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
        terminal.entry hfresh).1
  · exact
      (actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
        terminal.entry hbad).1

theorem ActualFPUTR1AtomOnlineFirstTerminal.classify_eq_terminal
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    (actualFPUTR1AtomOnlineMachine semantics completed).classify
        terminal.entry.stateBefore terminal.entry.occurrence =
          .freshHit terminal.owner terminal.payKey terminal.terminalPayload ∨
      (actualFPUTR1AtomOnlineMachine semantics completed).classify
        terminal.entry.stateBefore terminal.entry.occurrence =
          .bad terminal.owner terminal.payKey terminal.terminalPayload := by
  rcases terminal.transition_eq with hfresh | hbad
  · exact Or.inl
      (actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
        terminal.entry hfresh).2
  · exact Or.inr
      (actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
        terminal.entry hbad).2

private theorem ActualFPUTR1AtomOnlineFirstTerminal.entry_mem_trace
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    terminal.entry ∈
      (actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed) := by
  unfold ActualFPUTR1AtomOnlineFirstTerminal.entry
  exact List.get_mem _ _

theorem ActualFPUTR1AtomOnlineFirstTerminal.classify_eq_propose
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    (actualFPUTR1AtomOnlineMachine semantics completed).classify
        terminal.entry.stateBefore terminal.entry.occurrence =
      (actualFPUTR1AtomOnlineMachine semantics completed).propose
        terminal.entry.stateBefore terminal.entry.occurrence :=
  actualFPUTR1AtomOnline_trace_entry_classify_eq_propose
    semantics completed terminal.entry terminal.entry_mem_trace

/-- The exact labels stored by the terminal Cut datum are the selected
event's owner, structural key, and visible prefix payload. -/
theorem ActualFPUTR1AtomOnlineFirstTerminal.selected_labels
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    terminal.owner = terminal.entry.occurrence.owner ∧
      terminal.payKey = terminal.entry.occurrence.owner ∧
        terminal.terminalPayload = terminal.entry.occurrence.payload := by
  have hproposal :
      (actualFPUTR1AtomOnlineMachine semantics completed).propose
          terminal.entry.stateBefore terminal.entry.occurrence =
            .freshHit terminal.owner terminal.payKey terminal.terminalPayload ∨
        (actualFPUTR1AtomOnlineMachine semantics completed).propose
          terminal.entry.stateBefore terminal.entry.occurrence =
            .bad terminal.owner terminal.payKey terminal.terminalPayload := by
    rcases terminal.classify_eq_terminal with hfresh | hbad
    · exact Or.inl (terminal.classify_eq_propose.symm.trans hfresh)
    · exact Or.inr (terminal.classify_eq_propose.symm.trans hbad)
  rcases hproposal with hproposal | hproposal
  · have howner : terminal.entry.occurrence.owner = terminal.owner := by
      calc
        terminal.entry.occurrence.owner =
            ((actualFPUTR1AtomOnlineMachine semantics completed).propose
              terminal.entry.stateBefore terminal.entry.occurrence).owner :=
          (actualFPUTR1AtomOnlinePropose_owner semantics completed _ _).symm
        _ = terminal.owner := congrArg
          ActualFPUTOnlineMultiOpenTransition.owner hproposal
    have hpayKey : terminal.entry.occurrence.owner = terminal.payKey := by
      calc
        terminal.entry.occurrence.owner =
            ((actualFPUTR1AtomOnlineMachine semantics completed).propose
              terminal.entry.stateBefore terminal.entry.occurrence).payKey :=
          (actualFPUTR1AtomOnlinePropose_payKey semantics completed _ _).symm
        _ = terminal.payKey := congrArg
          ActualFPUTOnlineMultiOpenTransition.payKey hproposal
    have hpayload :
        terminal.entry.occurrence.payload = terminal.terminalPayload := by
      calc
        terminal.entry.occurrence.payload =
            ((actualFPUTR1AtomOnlineMachine semantics completed).propose
              terminal.entry.stateBefore terminal.entry.occurrence).payload :=
          (actualFPUTR1AtomOnlinePropose_payload semantics completed _ _).symm
        _ = terminal.terminalPayload := congrArg
          ActualFPUTOnlineMultiOpenTransition.payload hproposal
    exact ⟨howner.symm, hpayKey.symm, hpayload.symm⟩
  · have howner : terminal.entry.occurrence.owner = terminal.owner := by
      calc
        terminal.entry.occurrence.owner =
            ((actualFPUTR1AtomOnlineMachine semantics completed).propose
              terminal.entry.stateBefore terminal.entry.occurrence).owner :=
          (actualFPUTR1AtomOnlinePropose_owner semantics completed _ _).symm
        _ = terminal.owner := congrArg
          ActualFPUTOnlineMultiOpenTransition.owner hproposal
    have hpayKey : terminal.entry.occurrence.owner = terminal.payKey := by
      calc
        terminal.entry.occurrence.owner =
            ((actualFPUTR1AtomOnlineMachine semantics completed).propose
              terminal.entry.stateBefore terminal.entry.occurrence).payKey :=
          (actualFPUTR1AtomOnlinePropose_payKey semantics completed _ _).symm
        _ = terminal.payKey := congrArg
          ActualFPUTOnlineMultiOpenTransition.payKey hproposal
    have hpayload :
        terminal.entry.occurrence.payload = terminal.terminalPayload := by
      calc
        terminal.entry.occurrence.payload =
            ((actualFPUTR1AtomOnlineMachine semantics completed).propose
              terminal.entry.stateBefore terminal.entry.occurrence).payload :=
          (actualFPUTR1AtomOnlinePropose_payload semantics completed _ _).symm
        _ = terminal.terminalPayload := congrArg
          ActualFPUTOnlineMultiOpenTransition.payload hproposal
    exact ⟨howner.symm, hpayKey.symm, hpayload.symm⟩

/-- Open/read proposals are `ret`, so the first terminal occurrence must be
the close emitted by a completed owner. -/
theorem ActualFPUTR1AtomOnlineFirstTerminal.selected_kind_eq_close
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    terminal.entry.occurrence.kind = .close := by
  have hproposal :
      (actualFPUTR1AtomOnlineMachine semantics completed).propose
          terminal.entry.stateBefore terminal.entry.occurrence =
            .freshHit terminal.owner terminal.payKey terminal.terminalPayload ∨
        (actualFPUTR1AtomOnlineMachine semantics completed).propose
          terminal.entry.stateBefore terminal.entry.occurrence =
            .bad terminal.owner terminal.payKey terminal.terminalPayload := by
    rcases terminal.classify_eq_terminal with hfresh | hbad
    · exact Or.inl (terminal.classify_eq_propose.symm.trans hfresh)
    · exact Or.inr (terminal.classify_eq_propose.symm.trans hbad)
  by_cases hclose : terminal.entry.occurrence.kind = .close
  · exact hclose
  · have hret :
        (actualFPUTR1AtomOnlineMachine semantics completed).propose
            terminal.entry.stateBefore terminal.entry.occurrence =
          .ret terminal.entry.occurrence.owner
            terminal.entry.occurrence.owner
            terminal.entry.occurrence.payload := by
      cases hkind : terminal.entry.occurrence.kind <;>
        simp_all [actualFPUTR1AtomOnlineMachine,
          actualFPUTR1AtomOnlinePropose]
    rcases hproposal with hproposal | hproposal
    · rw [hret] at hproposal
      cases hproposal
    · rw [hret] at hproposal
      cases hproposal

/-- The first terminal close is exactly a strict-good or bad completed-owner
sector. -/
theorem ActualFPUTR1AtomOnlineFirstTerminal.selected_sector
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    completedCellSector (positiveRoutingSpec semantics)
          terminal.entry.occurrence.owner = .firstSeparatedQ1 ∨
      completedCellSector (positiveRoutingSpec semantics)
          terminal.entry.occurrence.owner = .bad := by
  have hsector := actualFPUTR1AtomOnline_closeProposedClass_eq_sector
    semantics completed terminal.entry.stateBefore terminal.entry.occurrence
      terminal.selected_kind_eq_close
  have hproposalClass :
      actualFPUTR1OnlineCompletedCellTransitionClass
          ((actualFPUTR1AtomOnlineMachine semantics completed).propose
            terminal.entry.stateBefore terminal.entry.occurrence) = .freshHit ∨
        actualFPUTR1OnlineCompletedCellTransitionClass
          ((actualFPUTR1AtomOnlineMachine semantics completed).propose
            terminal.entry.stateBefore terminal.entry.occurrence) = .bad := by
    rcases terminal.classify_eq_terminal with hfresh | hbad
    · left
      rw [← terminal.classify_eq_propose, hfresh]
      rfl
    · right
      rw [← terminal.classify_eq_propose, hbad]
      rfl
  have hsectorClass :
      actualFPUTR1OnlineCompletedCellClassOfSector
          (completedCellSector (positiveRoutingSpec semantics)
            terminal.entry.occurrence.owner) = .freshHit ∨
        actualFPUTR1OnlineCompletedCellClassOfSector
          (completedCellSector (positiveRoutingSpec semantics)
            terminal.entry.occurrence.owner) = .bad := by
    rcases hproposalClass with hfresh | hbad
    · exact Or.inl (hsector.symm.trans hfresh)
    · exact Or.inr (hsector.symm.trans hbad)
  cases hvalue : completedCellSector (positiveRoutingSpec semantics)
      terminal.entry.occurrence.owner with
  | pmem =>
      simp [hvalue, actualFPUTR1OnlineCompletedCellClassOfSector] at hsectorClass
  | firstSeparatedQ1 => exact Or.inl rfl
  | bad => exact Or.inr rfl

theorem actualFPUTR1AtomOnline_close_sector_eq_pmem_of_isRetOrPmem
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (entry : ActualFPUTOnlineMultiOpenTraceEntry
      (actualFPUTR1AtomOnlineMachine semantics completed))
    (hentry : entry ∈
      (actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed))
    (hclose : entry.occurrence.kind = .close)
    (hregular : actualFPUTOnlineMultiOpenTraceEntryIsRetOrPmem entry) :
    completedCellSector (positiveRoutingSpec semantics)
      entry.occurrence.owner = .pmem := by
  have hsector := actualFPUTR1AtomOnline_closeProposedClass_eq_sector
    semantics completed entry.stateBefore entry.occurrence hclose
  have hclassifyPropose := actualFPUTR1AtomOnline_trace_entry_classify_eq_propose
    semantics completed entry hentry
  rcases hregular with
    ⟨owner, payKey, payload, hret⟩ |
      ⟨owner, payKey, payload, hpmem⟩
  · have hclassify :=
      (actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
        entry hret).2
    have hproposal :
        (actualFPUTR1AtomOnlineMachine semantics completed).propose
            entry.stateBefore entry.occurrence = .ret owner payKey payload :=
      hclassifyPropose.symm.trans hclassify
    rw [hproposal] at hsector
    cases hvalue : completedCellSector (positiveRoutingSpec semantics)
        entry.occurrence.owner <;>
      simp [hvalue, actualFPUTR1OnlineCompletedCellTransitionClass,
        actualFPUTR1OnlineCompletedCellClassOfSector] at hsector
  · have hclassify :=
      (actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
        entry hpmem).2
    have hproposal :
        (actualFPUTR1AtomOnlineMachine semantics completed).propose
            entry.stateBefore entry.occurrence = .pmem owner payKey payload :=
      hclassifyPropose.symm.trans hclassify
    rw [hproposal] at hsector
    cases hvalue : completedCellSector (positiveRoutingSpec semantics)
        entry.occurrence.owner with
    | pmem => exact rfl
    | firstSeparatedQ1 =>
        simp [hvalue, actualFPUTR1OnlineCompletedCellTransitionClass,
          actualFPUTR1OnlineCompletedCellClassOfSector] at hsector
    | bad =>
        simp [hvalue, actualFPUTR1OnlineCompletedCellTransitionClass,
          actualFPUTR1OnlineCompletedCellClassOfSector] at hsector

/-- Earlier open/read events are `ret`; every earlier close is `pmem`. -/
theorem ActualFPUTR1AtomOnlineFirstTerminal.earlier_close_sector_eq_pmem
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed)
    (earlier : Fin
      ((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).length)
    (hearlier : earlier.1 < terminal.position.index.1)
    (hclose :
      (((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).get earlier).occurrence.kind =
          .close) :
    completedCellSector (positiveRoutingSpec semantics)
      (((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).get earlier).occurrence.owner =
        .pmem := by
  apply actualFPUTR1AtomOnline_close_sector_eq_pmem_of_isRetOrPmem
    semantics completed
  · exact List.get_mem _ _
  · exact hclose
  · exact terminal.earlier_isRetOrPmem earlier hearlier

/-! ## No-terminal branch and completed-owner partition -/

private theorem actualFPUTOnlineMultiOpenTraceFrom_all_isRetOrPmem_of_noTerminal
    {Occurrence Owner PayKey Payload : Type*}
    [DecidableEq Owner] [DecidableEq PayKey]
    (machine :
      ActualFPUTOnlineMultiOpenMachine Occurrence Owner PayKey Payload)
    (state : ActualFPUTOnlineMultiOpenState Owner PayKey Payload)
    (word : List Occurrence)
    (hstate : state.hitFlag = false)
    (hnoTerminal : ∀ entry ∈ machine.traceFrom state word,
      ¬ actualFPUTOnlineMultiOpenTraceEntryIsTerminal entry) :
    ∀ entry ∈ machine.traceFrom state word,
      actualFPUTOnlineMultiOpenTraceEntryIsRetOrPmem entry := by
  induction word generalizing state with
  | nil =>
      intro entry hentry
      simp [ActualFPUTOnlineMultiOpenMachine.traceFrom] at hentry
  | cons occurrence suffix induction =>
      let head : ActualFPUTOnlineMultiOpenTraceEntry machine :=
        { occurrence := occurrence
          stateBefore := state
          transition := some (machine.classify state occurrence)
          transition_spec := by simp [hstate] }
      have hdecomp : machine.traceFrom state (occurrence :: suffix) =
          head :: machine.traceFrom (machine.step state occurrence) suffix := by
        simp [ActualFPUTOnlineMultiOpenMachine.traceFrom, head, hstate]
      have hheadNotTerminal :
          ¬ actualFPUTOnlineMultiOpenTraceEntryIsTerminal head :=
        hnoTerminal head (by rw [hdecomp]; simp)
      have hheadLive : head.transition ≠ none := by
        simp [head]
      have hheadRegular :
          actualFPUTOnlineMultiOpenTraceEntryIsRetOrPmem head :=
        actualFPUTOnlineMultiOpenTraceEntry_isRetOrPmem_of_regular_live
          head hheadNotTerminal hheadLive
      have hnextState : (machine.step state occurrence).hitFlag = false := by
        rcases hheadRegular with
          ⟨owner, payKey, payload, hret⟩ |
            ⟨owner, payKey, payload, hpmem⟩
        · have hclassify :=
            (actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
              head hret).2
          change machine.classify state occurrence = .ret owner payKey payload at hclassify
          simp [ActualFPUTOnlineMultiOpenMachine.step, hstate, hclassify,
            applyActualFPUTOnlineMultiOpenTransition]
        · have hclassify :=
            (actualFPUTOnlineMultiOpenTraceEntry_classify_eq_of_transition_eq_some
              head hpmem).2
          change machine.classify state occurrence = .pmem owner payKey payload at hclassify
          simp [ActualFPUTOnlineMultiOpenMachine.step, hstate, hclassify,
            applyActualFPUTOnlineMultiOpenTransition]
      have htailNoTerminal :
          ∀ entry ∈ machine.traceFrom (machine.step state occurrence) suffix,
            ¬ actualFPUTOnlineMultiOpenTraceEntryIsTerminal entry := by
        intro entry hentry
        exact hnoTerminal entry (by
          rw [hdecomp]
          exact List.mem_cons_of_mem head hentry)
      intro entry hentry
      rw [hdecomp] at hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · exact hheadRegular
      · exact induction (machine.step state occurrence) hnextState
          htailNoTerminal entry hentry

theorem actualFPUTR1AtomOnline_noTerminal_all_traceEntries_isRetOrPmem
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (hnoTerminal :
      ¬ actualFPUTR1AtomOnlineTraceHasTerminal semantics completed) :
    ∀ entry ∈
        (actualFPUTR1AtomOnlineMachine semantics completed).trace
          (actualFPUTR1AtomOnlineEventWord completed),
      actualFPUTOnlineMultiOpenTraceEntryIsRetOrPmem entry := by
  apply actualFPUTOnlineMultiOpenTraceFrom_all_isRetOrPmem_of_noTerminal
    (actualFPUTR1AtomOnlineMachine semantics completed) .empty
      (actualFPUTR1AtomOnlineEventWord completed) rfl
  intro entry hentry hterminal
  apply hnoTerminal
  unfold actualFPUTR1AtomOnlineTraceHasTerminal
  unfold ActualFPUTOnlineMultiOpenMachine.trace
  rcases List.mem_iff_get.mp hentry with ⟨index, hindex⟩
  refine ⟨index, ?_⟩
  rw [hindex]
  exact hterminal

theorem actualFPUTR1AtomOnline_mem_eventWord_of_mem_eventsAt
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length)
    (event : ActualFPUTR1AtomOnlineEvent completed)
    (hevent : event ∈ actualFPUTR1AtomOnlineEventsAt completed atomPos) :
    event ∈ actualFPUTR1AtomOnlineEventWord completed := by
  rw [actualFPUTR1AtomOnlineEventWord, List.mem_flatten]
  refine ⟨actualFPUTR1AtomOnlineEventsAt completed atomPos, ?_, hevent⟩
  apply List.mem_map.mpr
  exact ⟨atomPos, List.mem_ofFn.mpr ⟨atomPos, rfl⟩, rfl⟩

theorem actualFPUTR1AtomOnline_exists_traceEntry_of_mem_eventWord
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (event : ActualFPUTR1AtomOnlineEvent completed)
    (hevent : event ∈ actualFPUTR1AtomOnlineEventWord completed) :
    ∃ entry : ActualFPUTOnlineMultiOpenTraceEntry
        (actualFPUTR1AtomOnlineMachine semantics completed),
      entry ∈ (actualFPUTR1AtomOnlineMachine semantics completed).trace
          (actualFPUTR1AtomOnlineEventWord completed) ∧
        entry.occurrence = event := by
  have hmapped : event ∈
      ((actualFPUTR1AtomOnlineMachine semantics completed).trace
        (actualFPUTR1AtomOnlineEventWord completed)).map
          (fun entry => entry.occurrence) := by
    rw [(actualFPUTR1AtomOnlineMachine semantics completed).trace_map_occurrence]
    exact hevent
  rcases List.mem_map.mp hmapped with ⟨entry, hentry, heq⟩
  exact ⟨entry, hentry, heq⟩

/-- If there is no live good-or-bad terminal, every completed owner closes
through `pmem`.  This quantifies over completed cells without identifying
their indices with trace positions. -/
theorem actualFPUTR1AtomOnline_all_completedCells_pmem_of_noTerminal
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (hnoTerminal :
      ¬ actualFPUTR1AtomOnlineTraceHasTerminal semantics completed) :
    ∀ cellIndex : Fin completed.word.cells.length,
      completedCellSector (positiveRoutingSpec semantics)
        (completed.word.cells.get cellIndex) = .pmem := by
  intro cellIndex
  rcases actualFPUTR1AtomOnline_existsUnique_close_of_completedCell
      completed cellIndex with ⟨atomPos, hcloseAt, _⟩
  let closeEvent := actualFPUTR1AtomOnlineEventAt completed atomPos .close
  have hword : closeEvent ∈ actualFPUTR1AtomOnlineEventWord completed :=
    actualFPUTR1AtomOnline_mem_eventWord_of_mem_eventsAt completed atomPos
      closeEvent hcloseAt.1
  rcases actualFPUTR1AtomOnline_exists_traceEntry_of_mem_eventWord
      semantics completed closeEvent hword with ⟨entry, hentry, hoccurrence⟩
  have hregular :=
    actualFPUTR1AtomOnline_noTerminal_all_traceEntries_isRetOrPmem
      semantics completed hnoTerminal entry hentry
  have hentryClose : entry.occurrence.kind = .close := by
    rw [hoccurrence]
    rfl
  have hsector := actualFPUTR1AtomOnline_close_sector_eq_pmem_of_isRetOrPmem
    semantics completed entry hentry hentryClose hregular
  have howner : entry.occurrence.owner =
      completed.word.cells.get cellIndex := by
    rw [hoccurrence]
    exact hcloseAt.2
  simpa [howner] using hsector

/-- Weakest order-correct finite partition: either the atom trace has its
canonical first terminal, or every completed-cell owner is `pmem`. -/
theorem actualFPUTR1AtomOnline_firstTerminal_or_allCompletedCellsPmem
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    Nonempty (ActualFPUTR1AtomOnlineFirstTerminal semantics completed) ∨
      ∀ cellIndex : Fin completed.word.cells.length,
        completedCellSector (positiveRoutingSpec semantics)
          (completed.word.cells.get cellIndex) = .pmem := by
  classical
  by_cases hterminal :
      actualFPUTR1AtomOnlineTraceHasTerminal semantics completed
  · exact Or.inl
      (nonempty_actualFPUTR1AtomOnlineFirstTerminal_of_hasTerminal
        semantics completed hterminal)
  · exact Or.inr
      (actualFPUTR1AtomOnline_all_completedCells_pmem_of_noTerminal
        semantics completed hterminal)

/-! ## Owner-only bridge to the completed word -/

/-- Each atom-position owner is exactly one completed-cell owner.  This is
an owner bijection statement, not an equality between the atom position and
the completed-cell scan rank. -/
theorem actualFPUTR1HoleToRootOwnerAt_existsUnique_completedCell
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length) :
    ∃! cellIndex : Fin completed.word.cells.length,
      actualFPUTR1HoleToRootOwnerAt completed atomPos =
        actualFPUTR1OnlineCompletedCellOwner completed cellIndex := by
  let atom := actualFPUTR1HoleToRootAtomAt completed atomPos
  rcases completed.fineAtom_mem_some_completedCell atom with
    ⟨cellIndex, hatomCell⟩
  have hatomOwner : atom ∈ actualFPUTR1HoleToRootOwnerAt completed atomPos := by
    change atom ∈ maximalPorousBlock readback.dependency atom
    exact anchor_mem_maximalPorousBlock readback.dependency atom
  have howner : actualFPUTR1HoleToRootOwnerAt completed atomPos =
      actualFPUTR1OnlineCompletedCellOwner completed cellIndex := by
    change actualFPUTR1HoleToRootOwnerAt completed atomPos =
      completed.word.cells.get cellIndex
    exact coefficientCompleteMacroCell_eq_of_commonOccurrence
      readback.dependency
        (actualFPUTR1HoleToRootOwnerAt_coefficientComplete completed atomPos)
        (completed.word.cell_complete cellIndex) hatomOwner hatomCell
  refine ⟨cellIndex, howner, ?_⟩
  intro other hother
  apply actualFPUTR1OnlineCompletedCellOwner_injective completed
  exact hother.symm.trans howner

/-- A close occurrence in the flattened event word is the canonical close
event at one literal atom position. -/
theorem actualFPUTR1AtomOnline_close_eq_eventAt_of_mem_eventWord
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback)
    (event : ActualFPUTR1AtomOnlineEvent completed)
    (hevent : event ∈ actualFPUTR1AtomOnlineEventWord completed)
    (hclose : event.kind = .close) :
    ∃ atomPos : Fin (actualFPUTR1HoleToRootAtomWord completed).length,
      event = actualFPUTR1AtomOnlineEventAt completed atomPos .close := by
  rw [actualFPUTR1AtomOnlineEventWord, List.mem_flatten] at hevent
  rcases hevent with ⟨bundle, hbundle, hevent⟩
  rcases List.mem_map.mp hbundle with ⟨atomPos, _, rfl⟩
  refine ⟨atomPos, ?_⟩
  classical
  by_cases hseen : actualFPUTR1HoleToRootOwnerSeenBefore completed atomPos
  · by_cases hcloses : actualFPUTR1HoleToRootClosesAt completed atomPos
    · simp [actualFPUTR1AtomOnlineEventsAt, hseen, hcloses] at hevent
      rcases hevent with hread | hcloseEvent
      · subst event
        simp [actualFPUTR1AtomOnlineEventAt] at hclose
      · exact hcloseEvent
    · simp [actualFPUTR1AtomOnlineEventsAt, hseen, hcloses] at hevent
      subst event
      simp [actualFPUTR1AtomOnlineEventAt] at hclose
  · by_cases hcloses : actualFPUTR1HoleToRootClosesAt completed atomPos
    · simp [actualFPUTR1AtomOnlineEventsAt, hseen, hcloses] at hevent
      rcases hevent with hopen | hcloseEvent
      · subst event
        simp [actualFPUTR1AtomOnlineEventAt] at hclose
      · exact hcloseEvent
    · simp [actualFPUTR1AtomOnlineEventsAt, hseen, hcloses] at hevent
      subst event
      simp [actualFPUTR1AtomOnlineEventAt] at hclose

/-- The terminal owner occurs at one unique completed-cell address.  Only
the owner is identified; the trace and completed-cell indices remain
different types and different orders. -/
theorem ActualFPUTR1AtomOnlineFirstTerminal.selectedOwner_existsUnique_completedCell
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (terminal : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    ∃! cellIndex : Fin completed.word.cells.length,
      terminal.entry.occurrence.owner =
        actualFPUTR1OnlineCompletedCellOwner completed cellIndex := by
  have hword : terminal.entry.occurrence ∈
      actualFPUTR1AtomOnlineEventWord completed := by
    have hmapped : terminal.entry.occurrence ∈
        ((actualFPUTR1AtomOnlineMachine semantics completed).trace
          (actualFPUTR1AtomOnlineEventWord completed)).map
            (fun entry => entry.occurrence) :=
      List.mem_map.mpr ⟨terminal.entry, terminal.entry_mem_trace, rfl⟩
    rw [(actualFPUTR1AtomOnlineMachine semantics completed).trace_map_occurrence]
      at hmapped
    exact hmapped
  rcases actualFPUTR1AtomOnline_close_eq_eventAt_of_mem_eventWord
      completed terminal.entry.occurrence hword terminal.selected_kind_eq_close
    with ⟨atomPos, hevent⟩
  rcases actualFPUTR1HoleToRootOwnerAt_existsUnique_completedCell
      completed atomPos with ⟨cellIndex, howner, hunique⟩
  refine ⟨cellIndex, ?_, ?_⟩
  · rw [hevent]
    exact howner
  · intro other hother
    apply hunique
    simpa [hevent] using hother

/-- Existence of a terminal is exactly failure of the order-independent
all-completed-cells-`pmem` alternative.  This statement deliberately maps
only owners, never first indices. -/
theorem actualFPUTR1AtomOnline_traceHasTerminal_iff_not_allCompletedCellsPmem
    (semantics : ActualFPUTR1PositiveRoutingSemantics readback)
    (completed : ActualFPUTR1IndexedFineFibreCompletedWord readback) :
    actualFPUTR1AtomOnlineTraceHasTerminal semantics completed ↔
      ¬ ∀ cellIndex : Fin completed.word.cells.length,
        completedCellSector (positiveRoutingSpec semantics)
          (completed.word.cells.get cellIndex) = .pmem := by
  constructor
  · intro hterminal hallPmem
    let terminal := actualFPUTR1AtomOnlineFirstTerminalOfHasTerminal
      semantics completed hterminal
    rcases terminal.selectedOwner_existsUnique_completedCell with
      ⟨cellIndex, howner, _⟩
    have hpmem := hallPmem cellIndex
    change completedCellSector (positiveRoutingSpec semantics)
      (actualFPUTR1OnlineCompletedCellOwner completed cellIndex) = .pmem at hpmem
    rw [← howner] at hpmem
    rcases terminal.selected_sector with hgood | hbad
    · exact ActualFPUTCompletedCellSector.noConfusion (hgood.symm.trans hpmem)
    · exact ActualFPUTCompletedCellSector.noConfusion (hbad.symm.trans hpmem)
  · intro hnotAllPmem
    by_contra hnoTerminal
    exact hnotAllPmem
      (actualFPUTR1AtomOnline_all_completedCells_pmem_of_noTerminal
        semantics completed hnoTerminal)

/-- Any two first-terminal certificates select the same payment labels.
This is the exact finite uniqueness needed by the Cut datum. -/
theorem actualFPUTR1AtomOnlineFirstTerminal_labels_unique
    {semantics : ActualFPUTR1PositiveRoutingSemantics readback}
    {completed : ActualFPUTR1IndexedFineFibreCompletedWord readback}
    (left right : ActualFPUTR1AtomOnlineFirstTerminal semantics completed) :
    left.owner = right.owner ∧ left.payKey = right.payKey ∧
      left.terminalPayload = right.terminalPayload := by
  have hindex := actualFPUTR1AtomOnlineFirstTerminal_index_unique left right
  have hentry : left.entry = right.entry := by
    unfold ActualFPUTR1AtomOnlineFirstTerminal.entry
    rw [hindex]
  have hleft := left.selected_labels
  have hright := right.selected_labels
  refine ⟨?_, ?_, ?_⟩
  · exact hleft.1.trans ((congrArg
      (fun entry => entry.occurrence.owner) hentry).trans hright.1.symm)
  · exact hleft.2.1.trans ((congrArg
      (fun entry => entry.occurrence.owner) hentry).trans hright.2.1.symm)
  · exact hleft.2.2.trans ((congrArg
      (fun entry => entry.occurrence.payload) hentry).trans hright.2.2.symm)

/-!
The construction above is finite and structural.  It does not discharge
`OPEN_measurability`, `OPEN_previsibility`, or `OPEN_actualReadSupport`, and
it makes no stopping-time or future-suffix freshness claim.  In particular,
a selected `bad` does not set the generic `hitFlag`; it is a Cut terminus,
not a frozen-state assertion.
-/

end

end ArchonPhysics.ActualFPUTR1AtomOnlineFirstTerminalCutGlue
