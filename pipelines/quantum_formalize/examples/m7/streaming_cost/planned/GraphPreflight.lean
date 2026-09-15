import M7StreamingCost

noncomputable def M7.StreamingCostTarget.cursor_projection : Prop :=
  ∀ (n : ℕ) (p : Fin n → M7.StreamingCost.Eval) (i fuel : ℕ), (M7.StreamingCost.allFinFrom n p i fuel).result = M7.StreamingIndices.allFinFrom n (fun j => (p j).result) i fuel

noncomputable def M7.StreamingCostTarget.cursor_bound : Prop :=
  ∀ (n : ℕ) (p : Fin n → M7.StreamingCost.Eval) (i fuel a b : ℕ), (∀ j, (p j).outer ≤ a ∧ (p j).inner ≤ b) → (M7.StreamingCost.allFinFrom n p i fuel).outer ≤ fuel*a ∧ (M7.StreamingCost.allFinFrom n p i fuel).inner ≤ fuel*b

noncomputable def M7.StreamingCostTarget.record_projection : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → M7.StreamingCost.Eval, (M7.StreamingCost.allRecords N p).result = M7.StreamingIndices.allRecords N (fun g => (p g).result)

noncomputable def M7.StreamingCostTarget.record_bound : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (p : M7.Action.Record N → M7.StreamingCost.Eval) (a b : ℕ), (∀ g, (p g).outer ≤ a ∧ (p g).inner ≤ b) → (M7.StreamingCost.allRecords N p).outer ≤ M7.StreamingCost.recordCount N*a ∧ (M7.StreamingCost.allRecords N p).inner ≤ M7.StreamingCost.recordCount N*b

noncomputable def M7.StreamingCostTarget.index_projection : Prop :=
  ∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval, (M7.StreamingCost.allIndices H N p).result = M7.StreamingIndices.allIndices H N (fun x => (p x).result)

noncomputable def M7.StreamingCostTarget.index_bound : Prop :=
  ∀ (H N : ℕ) [NeZero N], ∀ (p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval) (a b : ℕ), (∀ x, (p x).outer ≤ a ∧ (p x).inner ≤ b) → (M7.StreamingCost.allIndices H N p).outer ≤ (H * M7.StreamingCost.recordCount N)*a ∧ (M7.StreamingCost.allIndices H N p).inner ≤ (H * M7.StreamingCost.recordCount N)*b

noncomputable def M7.StreamingCostTarget.stream_projection_bound : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∀ x : M7.GlobalQuery.Index H N, (M7.StreamingCost.streamWin q bases x).result = M7.StreamingIndices.streamWin q bases x ∧ (M7.StreamingCost.streamWin q bases x).outer = 0 ∧ (M7.StreamingCost.streamWin q bases x).inner ≤ (H * M7.StreamingCost.recordCount N)

noncomputable def M7.StreamingCostTarget.scan_bound : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (M7.StreamingCost.scanWins q bases).outer ≤ (H * M7.StreamingCost.recordCount N) ∧ (M7.StreamingCost.scanWins q bases).inner ≤ (H * M7.StreamingCost.recordCount N)^2

noncomputable def M7.StreamingCostTarget.record_cardinality : Prop :=
  ∀ (N : ℕ) [NeZero N], M7.StreamingCost.recordCount N = Fintype.card (M7.Action.Record N) ∧ M7.StreamingCost.recordCount N = 2 * Nat.totient N * N^2

