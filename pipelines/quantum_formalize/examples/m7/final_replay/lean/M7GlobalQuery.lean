import M7DefaultQuery
namespace M7.GlobalQuery
abbrev Index (H N : ℕ) [NeZero N] := Fin H × M7.Action.Record N
abbrev Family (H N : ℕ) := Fin H → M7.Action.Recipe N
noncomputable def realize {H N : ℕ} [NeZero N] (bases : Family H N) (x : Index H N) : M7.Action.Recipe N := M7.Action.act x.2 (bases x.1)
noncomputable def feasible {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : Family H N) (x : Index H N) : Prop := M7.DefaultQuery.feasible q (bases x.1) (realize bases x)
noncomputable def objective {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : Family H N) (x : Index H N) : Fin q.objectives.length → ℤ := M7.DefaultQuery.objective q (realize bases x)
noncomputable def winners {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : Family H N) : Finset (Index H N) := M7.Selection.select Finset.univ (feasible q bases) (objective q bases) q.order
noncomputable def winningClasses {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : Family H N) : Finset (Fin H) := (winners q bases).image Prod.fst
noncomputable def present {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : Family H N) (x : Index H N) : Prop := x ∈ winners q bases ∧ M7.ActualPresentation.leastAction (bases x.1) (realize bases x) = some x.2
/-- A structural intermediate property, to be proved for the actual generated canonical family. -/
noncomputable def separated {H N : ℕ} [NeZero N] (bases : Family H N) : Prop := ∀ x y : Index H N, realize bases x = realize bases y → x.1 = y.1
noncomputable def answer {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : Family H N) : Except M7.DefaultQuery.QueryError (Finset (Index H N)) := by
  classical
  exact if M7.DefaultQuery.valid N q then .ok (winners q bases) else .error .invalidSignature
end M7.GlobalQuery
