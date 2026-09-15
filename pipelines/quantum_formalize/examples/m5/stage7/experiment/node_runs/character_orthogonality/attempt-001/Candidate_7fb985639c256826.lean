import FrozenTarget_7fb985639c256826
theorem M5.Character.character_orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ (D : ℕ) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z) = if z = 0 then (2 : ℤ) ^ D else 0
  intro D z
  classical
  change (∑ lam : Fin D → ZMod 2, ∏ i : Fin D, M5.Character.bitSign (lam i) (z i)) = if z = 0 then (2 : ℤ) ^ D else 0
  rw [← Fintype.prod_sum]
  simp_rw [M5.Character.bit_orthogonality]
  by_cases hz : z = 0
  · subst z
    simp
  · rw [if_neg hz]
    have hn : ∃ i : Fin D, z i ≠ 0 := by
      by_contra! h
      apply hz
      funext i
      exact h i
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
