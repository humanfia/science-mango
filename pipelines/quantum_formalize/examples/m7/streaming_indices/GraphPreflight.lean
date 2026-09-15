import M7StreamingIndices
def target_0 : Prop := (∀ (n : ℕ) (p : Fin n → Bool) (i fuel : ℕ), M7.StreamingIndices.allFinFrom n p i fuel = true ↔ ∀ j : Fin n, i ≤ j.val → j.val < i + fuel → p j = true)
def target_1 : Prop := (∀ (n : ℕ) (p : Fin n → Bool), M7.StreamingIndices.allFin n p = true ↔ ∀ j : Fin n, p j = true)
def target_2 : Prop := (∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, ∃ (u : Fin (Fintype.card ((ZMod N)ˣ))) (e : Fin 2) (s t : Fin N), M7.StreamingIndices.decodeRecord N u e s t = g)
def target_3 : Prop := (∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → Bool, M7.StreamingIndices.allRecords N p = true ↔ ∀ g : M7.Action.Record N, p g = true)
def target_4 : Prop := (∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → Bool, M7.StreamingIndices.allIndices H N p = true ↔ ∀ x : M7.GlobalQuery.Index H N, p x = true)
def target_5 : Prop := (∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.StreamingIndices.streamWin q bases x = true ↔ x ∈ M7.GlobalQuery.winners q bases)
