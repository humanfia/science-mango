import FrozenTarget_396ee5306757abd4
theorem M7.PrefixBits.leaf_undecided : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, p.length = M7.PrefixBits.depth N → M7.PrefixBits.WA N p = ∅ ∧ M7.PrefixBits.WB N p = ∅
  intro N hN p hp
  unfold M7.PrefixBits.depth at hp
  unfold M7.PrefixBits.WA M7.PrefixBits.WB M7.PrefixBits.undecided
  constructor <;> apply Finset.eq_empty_iff_forall_not_mem.mpr <;> intro x hx
  all_goals
    rcases Finset.mem_image.mp hx with ⟨j, hj, hje⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    omega
