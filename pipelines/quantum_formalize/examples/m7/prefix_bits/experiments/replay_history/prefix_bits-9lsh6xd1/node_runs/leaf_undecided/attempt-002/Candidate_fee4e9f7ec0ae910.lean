import FrozenTarget_fee4e9f7ec0ae910
theorem M7.PrefixBits.leaf_undecided : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, p.length = M7.PrefixBits.depth N → M7.PrefixBits.WA N p = ∅ ∧ M7.PrefixBits.WB N p = ∅
  intro N hN p hp
  unfold M7.PrefixBits.depth at hp
  constructor <;> apply Finset.ext <;> intro x
  all_goals
    simp only [M7.PrefixBits.WA, M7.PrefixBits.WB, M7.PrefixBits.undecided,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_empty]
    constructor
    · rintro ⟨j, ⟨hj, hremaining⟩, heq⟩
      omega
    · intro h
      exact h.elim
