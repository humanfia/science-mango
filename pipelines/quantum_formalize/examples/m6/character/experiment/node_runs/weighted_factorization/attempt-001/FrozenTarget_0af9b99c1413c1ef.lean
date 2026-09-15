import M6Character

theorem M6.Character.sign_add : ∀ (a b : ZMod 2), M6.Character.sign (a+b) = M6.Character.sign a * M6.Character.sign b := by
  change ∀ (a b : ZMod 2), M6.Character.sign (a + b) = M6.Character.sign a * M6.Character.sign b
  intro a b
  fin_cases a <;> fin_cases b <;> decide

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (w : Fin m → ZMod 2 → Polynomial ℤ) (q : M6.Character.Vector m), M6.Character.localTransform w q = ∑ z : M6.Character.Vector m, Polynomial.C (M6.Character.character q z) * ∏ i, w i (z i)
