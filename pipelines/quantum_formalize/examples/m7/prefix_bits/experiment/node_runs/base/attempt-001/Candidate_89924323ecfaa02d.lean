import FrozenTarget_89924323ecfaa02d
theorem M7.PrefixBits.base : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, M7.PrefixCompleted.Base N (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p)
  intro N hN p
  classical
  have hs (o : ℕ) : M7.PrefixBits.selected N o p ⊆ Finset.range N := by
    intro x hx
    simp only [M7.PrefixBits.selected, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx
    apply Finset.mem_range.mpr
    rcases hx with rfl | ⟨j, ⟨hj, _⟩, rfl⟩
    · exact hN
    · omega
  have hu (o : ℕ) : M7.PrefixBits.undecided N o p ⊆ Finset.range N := by
    intro x hx
    simp only [M7.PrefixBits.undecided, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hx
    rcases hx with ⟨j, ⟨hj, _⟩, rfl⟩
    apply Finset.mem_range.mpr
    omega
  have hz (o : ℕ) : 0 ∈ M7.PrefixBits.selected N o p := by
    simp [M7.PrefixBits.selected]
  have hd (o : ℕ) : Disjoint (M7.PrefixBits.selected N o p) (M7.PrefixBits.undecided N o p) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [M7.PrefixBits.selected, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx
    simp only [M7.PrefixBits.undecided, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hy
    rcases hy with ⟨k, ⟨hk, hku⟩, hke⟩
    rcases hx with hx | ⟨j, ⟨hj, hjd, hjb⟩, hje⟩
    · omega
    · omega
  have hs0 := hs 0
  have hs1 := hs (N - 1)
  have hu0 := hu 0
  have hu1 := hu (N - 1)
  have hz0 := hz 0
  have hz1 := hz (N - 1)
  have hd0 := hd 0
  have hd1 := hd (N - 1)
  unfold M7.PrefixCompleted.Base
  simp only [M7.PrefixBits.A, M7.PrefixBits.B, M7.PrefixBits.WA, M7.PrefixBits.WB]
  aesop
