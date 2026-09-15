import FrozenTarget_524737928f76decd
theorem M7.Supports.degree_lt : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).natDegree < N
  intro N inst A
  by_cases h : M7.Supports.polynomial A = 0
  · simpa [h] using (Nat.pos_of_ne_zero (NeZero.ne N))
  · have hm := Polynomial.natDegree_mem_support_of_nonzero h
    rw [M7.Supports.support N A] at hm
    change (M7.Supports.polynomial A).natDegree ∈ A.image ZMod.val at hm
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
    rw [← heq]
    exact ZMod.val_lt i
