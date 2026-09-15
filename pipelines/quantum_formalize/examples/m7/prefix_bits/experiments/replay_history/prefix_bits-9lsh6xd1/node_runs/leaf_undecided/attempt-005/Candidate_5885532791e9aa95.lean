import FrozenTarget_5885532791e9aa95
theorem M7.PrefixBits.leaf_undecided : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, p.length = M7.PrefixBits.depth N → M7.PrefixBits.WA N p = ∅ ∧ M7.PrefixBits.WB N p = ∅
  intro N hN p hp
  unfold M7.PrefixBits.depth at hp
  unfold M7.PrefixBits.WA M7.PrefixBits.WB M7.PrefixBits.undecided
  constructor <;>
    (apply Finset.ext
     intro x
     constructor
     · intro hx
       rcases Finset.mem_image.mp hx with ⟨j, hj, heq⟩
       rcases Finset.mem_filter.mp hj with ⟨hj, hlen⟩
       have hj' := Finset.mem_range.mp hj
       omega
     · intro hx
       simp at hx)
