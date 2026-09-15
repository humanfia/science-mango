import M7GlobalQuery
import M7SelectionAccepted
import M7ActualPresentationAccepted

noncomputable def M7.GlobalQueryTarget.winners_exact : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (∀ x : M7.GlobalQuery.Index H N, x ∈ M7.GlobalQuery.winners q bases ↔ M7.GlobalQuery.feasible q bases x ∧ ∀ y : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases y → ¬ M7.Selection.better q.order (M7.GlobalQuery.objective q bases y) (M7.GlobalQuery.objective q bases x)) ∧ (M7.GlobalQuery.winners q bases = ∅ ↔ ¬ ∃ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases x)

#check M7.GlobalQueryTarget.winners_exact

noncomputable def M7.GlobalQueryTarget.strict_dominator : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.feasible q bases x → x ∉ M7.GlobalQuery.winners q bases → ∃ y ∈ M7.GlobalQuery.winners q bases, M7.Selection.better q.order (M7.GlobalQuery.objective q bases y) (M7.GlobalQuery.objective q bases x)

#check M7.GlobalQueryTarget.strict_dominator

noncomputable def M7.GlobalQueryTarget.winning_classes : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (i : Fin H), i ∈ M7.GlobalQuery.winningClasses q bases ↔ ∃ g : M7.Action.Record N, (i,g) ∈ M7.GlobalQuery.winners q bases

#check M7.GlobalQueryTarget.winning_classes

noncomputable def M7.GlobalQueryTarget.winning_fiber : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x y : M7.GlobalQuery.Index H N), x.1 = y.1 → M7.GlobalQuery.realize bases x = M7.GlobalQuery.realize bases y → (x ∈ M7.GlobalQuery.winners q bases ↔ y ∈ M7.GlobalQuery.winners q bases)

#check M7.GlobalQueryTarget.winning_fiber

noncomputable def M7.GlobalQueryTarget.presentation_sound : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.present q bases x → x ∈ M7.GlobalQuery.winners q bases ∧ ∀ g : M7.Action.Record N, M7.Action.act g (bases x.1) = M7.GlobalQuery.realize bases x → M7.ActualPresentation.encode x.2 ≤ M7.ActualPresentation.encode g

#check M7.GlobalQueryTarget.presentation_sound

noncomputable def M7.GlobalQueryTarget.same_class_presentation : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), x ∈ M7.GlobalQuery.winners q bases → ∃! g : M7.Action.Record N, M7.GlobalQuery.present q bases (x.1,g) ∧ M7.Action.act g (bases x.1) = M7.GlobalQuery.realize bases x

#check M7.GlobalQueryTarget.same_class_presentation

noncomputable def M7.GlobalQueryTarget.physical_presentation : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), M7.GlobalQuery.separated bases → ∀ x ∈ M7.GlobalQuery.winners q bases, ∃! y : M7.GlobalQuery.Index H N, M7.GlobalQuery.present q bases y ∧ M7.GlobalQuery.realize bases y = M7.GlobalQuery.realize bases x

#check M7.GlobalQueryTarget.physical_presentation

noncomputable def M7.GlobalQueryTarget.empty_objectives : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), q.objectives = [] → M7.GlobalQuery.winners q bases = M7.Selection.feasibleSet Finset.univ (M7.GlobalQuery.feasible q bases)

#check M7.GlobalQueryTarget.empty_objectives

noncomputable def M7.GlobalQueryTarget.invalid_rejection : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (¬ M7.DefaultQuery.valid N q → M7.GlobalQuery.answer q bases = Except.error M7.DefaultQuery.QueryError.invalidSignature ∧ M7.GlobalQuery.winners q bases = ∅) ∧ (M7.DefaultQuery.valid N q → M7.GlobalQuery.answer q bases = Except.ok (M7.GlobalQuery.winners q bases))

#check M7.GlobalQueryTarget.invalid_rejection

