import FrozenTarget_f603029eef14a02e
theorem M7.PrefixBits.leaf_undecided : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, p.length = M7.PrefixBits.depth N → M7.PrefixBits.WA N p = ∅ ∧ M7.PrefixBits.WB N p = ∅
  intro N hN p hp
  unfold M7.PrefixBits.depth at hp
  constructor <;> apply Finset.eq_empty_iff_forall_not_mem.mpr
  all_goals
    intro x hx
    simp only [M7.PrefixBits.WA, M7.PrefixBits.WB, M7.PrefixBits.undecided,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx
    rcases hx with ⟨j, ⟨hj, hremaining⟩, hji⟩
    omega
