import FrozenTarget_0c91378c8f547ba3
theorem M6.Character.orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (z : M6.Character.Vector m), M6.Character.characterSum D z = M6.Character.orthogonalIndicator D z
  intro m D z
  classical
  have hmem (q : M6.Character.Vector m) : q ∈ M6.Character.subspaceWords D ↔ q ∈ D := by
    simp [M6.Character.subspaceWords]
  unfold M6.Character.characterSum M6.Character.orthogonalIndicator
  by_cases h : M6.Character.Orthogonal D z
  · rw [if_pos h]
    have hone : ∀ q ∈ M6.Character.subspaceWords D, M6.Character.character q z = 1 := by
      intro q hq
      apply (M6.Character.sign_eq_one _).1.mpr
      exact h q ((hmem q).mp hq)
    simp only [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    obtain ⟨q₀, hq₀, hn⟩ : ∃ q₀ ∈ D, M6.Character.dot q₀ z ≠ 0 := by
      simpa only [M6.Character.Orthogonal, not_forall, not_imp] using h
    have hc : M6.Character.character q₀ z = -1 :=
      (M6.Character.sign_eq_one _).2.mpr hn
    have ht : (∑ q ∈ M6.Character.subspaceWords D, M6.Character.character (q₀ + q) z) =
        ∑ q ∈ M6.Character.subspaceWords D, M6.Character.character q z := by
      refine Finset.sum_bij (fun q _ => q₀ + q) ?_ ?_ ?_ ?_
      · intro q hq
        exact (hmem _).mpr (D.add_mem hq₀ ((hmem q).mp hq))
      · intro a ha b hb hab
        exact add_left_cancel hab
      · intro q hq
        refine ⟨q - q₀, (hmem _).mpr (D.sub_mem ((hmem q).mp hq) hq₀), ?_⟩
        simp [add_comm]
      · intro q hq
        rfl
    simp only [M6.Character.character_add, hc, neg_one_mul, Finset.sum_neg_distrib] at ht
    omega
