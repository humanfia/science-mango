import FrozenTarget_6fe3c4870d07c7b7
theorem M6.Character.orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (z : M6.Character.Vector m), M6.Character.characterSum D z = M6.Character.orthogonalIndicator D z
  classical
  intro m D z
  unfold M6.Character.orthogonalIndicator
  by_cases h : M6.Character.Orthogonal D z
  · rw [if_pos h]
    have hc : ∀ q ∈ M6.Character.subspaceWords D, M6.Character.character q z = 1 := by
      intro q hq
      apply ((M6.Character.sign_eq_one (M6.Character.dot q z)).1).2
      exact h q (by simpa [M6.Character.subspaceWords] using hq)
    simp [M6.Character.characterSum, hc]
  · rw [if_neg h]
    have hex : ∃ q₀ ∈ D, M6.Character.dot q₀ z ≠ 0 := by
      by_contra hn
      apply h
      intro q hq
      by_contra hd
      exact hn ⟨q, hq, hd⟩
    obtain ⟨q₀, hq₀, hd⟩ := hex
    have hc : M6.Character.character q₀ z = -1 :=
      ((M6.Character.sign_eq_one (M6.Character.dot q₀ z)).2).2 hd
    have hmem : ∀ q, q ∈ M6.Character.subspaceWords D ↔ q ∈ D := by
      intro q
      simp [M6.Character.subspaceWords]
    have ht :
        (∑ q ∈ M6.Character.subspaceWords D, M6.Character.character (q₀ + q) z) =
        ∑ q ∈ M6.Character.subspaceWords D, M6.Character.character q z := by
      refine Finset.sum_bij (fun q _ => q₀ + q) ?_ ?_ ?_ ?_
      · intro q hq
        exact (hmem _).2 (D.add_mem hq₀ ((hmem q).1 hq))
      · intro a ha b hb hab
        exact add_left_cancel hab
      · intro q hq
        refine ⟨-q₀ + q, (hmem _).2 (D.add_mem (D.neg_mem hq₀) ((hmem q).1 hq)), ?_⟩
        simp [← add_assoc]
      · intro q hq
        rfl
    simp_rw [M6.Character.character_add, hc, neg_one_mul] at ht
    rw [Finset.sum_neg_distrib] at ht
    unfold M6.Character.characterSum
    linarith
