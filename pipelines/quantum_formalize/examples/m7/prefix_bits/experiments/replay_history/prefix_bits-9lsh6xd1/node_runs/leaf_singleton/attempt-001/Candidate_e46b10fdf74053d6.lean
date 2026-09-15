import FrozenTarget_e46b10fdf74053d6
theorem M7.PrefixBits.leaf_singleton : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ), 0 < N → ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length = M7.PrefixBits.depth N → M7.PrefixBits.completed N w E p ⊆ {(M7.PrefixBits.A N p, M7.PrefixBits.B N p)}
  intro N hN w E p hp
  classical
  obtain ⟨hWA, hWB⟩ := M7.PrefixBits.leaf_undecided N hN p hp
  intro x hx
  unfold M7.PrefixBits.completed at hx
  rw [hWA, hWB] at hx
  have h := ((M7.PrefixCompleted.completed_membership N w E
    (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) ∅ ∅
    (by simp) (by simp) x).mp hx).1
  simp only [M7.PrefixCompleted.Within, Finset.union_empty] at h
  apply Finset.mem_singleton.mpr
  apply Prod.ext
  · apply Finset.Subset.antisymm <;> tauto
  · apply Finset.Subset.antisymm <;> tauto
