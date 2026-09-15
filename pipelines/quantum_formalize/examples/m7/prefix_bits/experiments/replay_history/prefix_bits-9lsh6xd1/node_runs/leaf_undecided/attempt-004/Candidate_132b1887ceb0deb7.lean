import FrozenTarget_132b1887ceb0deb7
theorem M7.PrefixBits.leaf_undecided : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, p.length = M7.PrefixBits.depth N → M7.PrefixBits.WA N p = ∅ ∧ M7.PrefixBits.WB N p = ∅
  intro N hN p hp
  change p.length = 2 * (N - 1) at hp
  constructor <;> apply Finset.ext <;> intro x
  all_goals
    simp only [M7.PrefixBits.WA, M7.PrefixBits.WB, M7.PrefixBits.undecided,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      Finset.not_mem_empty, iff_false]
    rintro ⟨j, ⟨hj, hremaining⟩, hₓ⟩
    omega
