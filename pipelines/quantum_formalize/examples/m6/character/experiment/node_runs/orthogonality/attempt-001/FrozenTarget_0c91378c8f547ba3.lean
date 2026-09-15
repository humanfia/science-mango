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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (z : M6.Character.Vector m), M6.Character.characterSum D z = M6.Character.orthogonalIndicator D z
