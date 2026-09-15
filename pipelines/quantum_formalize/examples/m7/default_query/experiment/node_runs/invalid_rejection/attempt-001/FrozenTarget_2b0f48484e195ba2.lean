import M7ActualPresentationAccepted
import M7DefaultQuery
import M7SelectionAccepted

theorem M7.DefaultQuery.winners_exact : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g : M7.Action.Record N, g ∈ M7.DefaultQuery.winners q base ↔ M7.DefaultQuery.feasible q base (M7.Action.act g base) ∧ ∀ h : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act h base) → ¬ M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base))) ∧ (M7.DefaultQuery.winners q base = ∅ ↔ ¬ ∃ g : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act g base)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g : M7.Action.Record N, g ∈ M7.DefaultQuery.winners q base ↔ M7.DefaultQuery.feasible q base (M7.Action.act g base) ∧ ∀ h : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act h base) → ¬ M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base))) ∧ (M7.DefaultQuery.winners q base = ∅ ↔ ¬ ∃ g : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act g base))
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro N inst q base
  simpa [M7.DefaultQuery.winners, M7.ActualPresentation.selected,
    M7.Selection.feasibleSet, Finset.filter_eq_empty_iff] using
    (M7.Selection.selector_exact (M7.Action.Record N) q.objectives.length
      (Finset.univ : Finset (M7.Action.Record N))
      (fun g => M7.DefaultQuery.feasible q base (M7.Action.act g base))
      (fun g => M7.DefaultQuery.objective q (M7.Action.act g base)) q.order)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (¬ M7.DefaultQuery.valid N q → M7.DefaultQuery.answer q base = Except.error M7.DefaultQuery.QueryError.invalidSignature ∧ M7.DefaultQuery.winners q base = ∅) ∧ (M7.DefaultQuery.valid N q → M7.DefaultQuery.answer q base = Except.ok (M7.DefaultQuery.winners q base))
