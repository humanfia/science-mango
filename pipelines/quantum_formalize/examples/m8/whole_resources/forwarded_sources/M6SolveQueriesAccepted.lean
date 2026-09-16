import M6SolveResources

theorem M6.ActualTransfer.actual_solve_queries : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) → k ≤ 2*N := by
  intro N inst a b d v k h
  have hbound : ∀ c : M6.Pinned.Pins (2*N) → ℤ,
      (M6.Pinned.recover c (M6.Pinned.free (2*N)) (List.finRange (2*N))).2 ≤ 2*N := by
    intro c
    simpa using (M6.Pinned.recover_properties (2*N) c
      (M6.Pinned.free (2*N)) (List.finRange (2*N))).2.2
  unfold M6.ActualTransfer.solve M6.Pinned.solve at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨hd, hv, hk⟩
    rw [← hk]
    exact hbound _
#print axioms M6.ActualTransfer.actual_solve_queries
