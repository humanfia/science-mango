import M6Character

theorem M6.Character.sign_add : ∀ (a b : ZMod 2), M6.Character.sign (a+b) = M6.Character.sign a * M6.Character.sign b := by
  change ∀ (a b : ZMod 2), M6.Character.sign (a + b) = M6.Character.sign a * M6.Character.sign b
  intro a b
  fin_cases a <;> fin_cases b <;> decide

theorem M6.Character.sign_eq_one : ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0) := by
  change ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0)
  intro a
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl <;> norm_num [M6.Character.sign, ZMod.val_zero, ZMod.val_one_eq_one_mod]

theorem M6.Character.character_add : ∀ (m : ℕ) (q r z : M6.Character.Vector m), M6.Character.character (q+r) z = M6.Character.character q z * M6.Character.character r z := by
  change ∀ (m : ℕ) (q r z : M6.Character.Vector m), M6.Character.character (q + r) z = M6.Character.character q z * M6.Character.character r z
  intro m q r z
  simp only [M6.Character.character, M6.Character.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib, M6.Character.sign_add]

theorem M6.Character.sign_sum : ∀ (m : ℕ) (f : Fin m → ZMod 2), M6.Character.sign (∑ i, f i) = ∏ i, M6.Character.sign (f i) := by
  change ∀ (m : ℕ) (f : Fin m → ZMod 2), M6.Character.sign (∑ i, f i) = ∏ i, M6.Character.sign (f i)
  intro m f
  have h : ∀ s : Finset (Fin m), M6.Character.sign (∑ i ∈ s, f i) = ∏ i ∈ s, M6.Character.sign (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, Finset.prod_empty]
        decide
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, M6.Character.sign_add, ih]
  exact h Finset.univ

theorem M6.Character.character_product : ∀ (m : ℕ) (q z : M6.Character.Vector m), M6.Character.character q z = ∏ i, M6.Character.sign (q i * z i) := by
  change ∀ (m : ℕ) (q z : M6.Character.Vector m), M6.Character.character q z = ∏ i, M6.Character.sign (q i * z i)
  intro m q z
  change M6.Character.sign (∑ i, q i * z i) = ∏ i, M6.Character.sign (q i * z i)
  exact M6.Character.sign_sum m (fun i => q i * z i)

theorem M6.Character.orthogonality : ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (z : M6.Character.Vector m), M6.Character.characterSum D z = M6.Character.orthogonalIndicator D z := by
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

theorem M6.Character.weighted_factorization : ∀ (m : ℕ) (w : Fin m → ZMod 2 → Polynomial ℤ) (q : M6.Character.Vector m), M6.Character.localTransform w q = ∑ z : M6.Character.Vector m, Polynomial.C (M6.Character.character q z) * ∏ i, w i (z i) := by
  change ∀ (m : ℕ) (w : Fin m → ZMod 2 → Polynomial ℤ) (q : M6.Character.Vector m), M6.Character.localTransform w q = ∑ z : M6.Character.Vector m, Polynomial.C (M6.Character.character q z) * ∏ i, w i (z i)
  intro m w q
  classical
  unfold M6.Character.localTransform
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [M6.Character.character_product, map_prod, Finset.prod_mul_distrib, mul_comm]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (w : Fin m → ZMod 2 → Polynomial ℤ), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Character.weightedDual D w = M6.Character.weightedTransform D w
