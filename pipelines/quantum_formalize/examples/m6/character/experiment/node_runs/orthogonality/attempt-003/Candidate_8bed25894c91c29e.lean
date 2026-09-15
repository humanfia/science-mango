import FrozenTarget_8bed25894c91c29e
theorem M6.Character.orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (z : M6.Character.Vector m), M6.Character.characterSum D z = M6.Character.orthogonalIndicator D z
  intro m D z
  classical
  have mem_words (q : M6.Character.Vector m) : q ∈ M6.Character.subspaceWords D ↔ q ∈ D := by
    simp [M6.Character.subspaceWords]
  unfold M6.Character.orthogonalIndicator
  by_cases h : M6.Character.Orthogonal D z
  · rw [if_pos h]
    have hc : ∀ q ∈ M6.Character.subspaceWords D, M6.Character.character q z = 1 := by
      intro q hq
      apply (M6.Character.sign_eq_one _).1.mpr
      exact h q ((mem_words q).mp hq)
    unfold M6.Character.characterSum
    calc
      ∑ q ∈ M6.Character.subspaceWords D, M6.Character.character q z =
          ∑ q ∈ M6.Character.subspaceWords D, (1 : ℤ) := Finset.sum_congr rfl hc
      _ = _ := by simp
  · rw [if_neg h]
    unfold M6.Character.Orthogonal at h
    push_neg at h
    obtain ⟨q0, hq0, hne⟩ := h
    have hs : M6.Character.character q0 z = -1 :=
      (M6.Character.sign_eq_one _).2.mpr hne
    have ht : (∑ q ∈ M6.Character.subspaceWords D, M6.Character.character (q0 + q) z) =
        ∑ q ∈ M6.Character.subspaceWords D, M6.Character.character q z := by
      refine Finset.sum_bij (fun q _ => q0 + q) ?_ ?_ ?_ ?_
      · intro q hq
        exact (mem_words _).mpr (D.add_mem hq0 ((mem_words q).mp hq))
      · intro q hq r hr heq
        exact add_left_cancel heq
      · intro q hq
        refine ⟨q - q0, (mem_words _).mpr (D.sub_mem ((mem_words q).mp hq) hq0), ?_⟩
        abel
      · intro q hq
        rfl
    simp only [M6.Character.character_add, hs, neg_one_mul, Finset.sum_neg_distrib] at ht
    unfold M6.Character.characterSum
    omega
