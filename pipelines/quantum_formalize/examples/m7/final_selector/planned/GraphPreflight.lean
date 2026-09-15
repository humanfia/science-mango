import M7FinalSelector

noncomputable def M7.FinalSelectorTarget.raw_realizable : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c → ∃ x : M7.FinalSelector.Index N w q, M7.FinalSelector.realize q x = c

noncomputable def M7.FinalSelectorTarget.index_feasible : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ x : M7.FinalSelector.Index N w q, M7.GlobalQuery.feasible q (M7.FinalSelector.family N w q) x ↔ M7.FinalSelector.RawFeasible w q (M7.FinalSelector.realize q x)

noncomputable def M7.FinalSelectorTarget.winner_exact : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = true ↔ M7.FinalSelector.RawWinner w q (M7.FinalSelector.realize q x)

noncomputable def M7.FinalSelectorTarget.raw_output : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ c : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q c ↔ ∃ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = true ∧ M7.FinalSelector.realize q x = c

noncomputable def M7.FinalSelectorTarget.presentation_exact : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ c : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q c ↔ ∃! x : M7.FinalSelector.Index N w q, M7.FinalSelector.present q x = true ∧ M7.FinalSelector.realize q x = c

noncomputable def M7.FinalSelectorTarget.empty_exact : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ((∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = false) ↔ ¬ ∃ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c)

noncomputable def M7.FinalSelectorTarget.strict_dominator : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c → ¬ M7.FinalSelector.RawWinner w q c → ∃ d : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q d ∧ M7.Selection.better q.order (M7.DefaultQuery.objective q d) (M7.DefaultQuery.objective q c)

noncomputable def M7.FinalSelectorTarget.invalid_rejection : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), (¬ M7.DefaultQuery.valid N q) → (∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.answer q x = Except.error M7.DefaultQuery.QueryError.invalidSignature) ∧ (¬ ∃ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c)

