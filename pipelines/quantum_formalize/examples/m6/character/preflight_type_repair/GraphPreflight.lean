import M6Character
open scoped BigOperators
def target_0 : Prop := ∀ (a b : ZMod 2), M6.Character.sign (a+b) = M6.Character.sign a * M6.Character.sign b
#check target_0
def target_1 : Prop := ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0)
#check target_1
def target_2 : Prop := ∀ (m : ℕ) (f : Fin m → ZMod 2), M6.Character.sign (∑ i, f i) = ∏ i, M6.Character.sign (f i)
#check target_2
def target_3 : Prop := ∀ (m : ℕ) (q r z : M6.Character.Vector m), M6.Character.character (q+r) z = M6.Character.character q z * M6.Character.character r z
#check target_3
def target_4 : Prop := ∀ (m : ℕ) (q z : M6.Character.Vector m), M6.Character.character q z = ∏ i, M6.Character.sign (q i * z i)
#check target_4
def target_5 : Prop := ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (z : M6.Character.Vector m), M6.Character.characterSum D z = if M6.Character.Orthogonal D z then (M6.Character.subspaceWords D).card else 0
#check target_5
def target_6 : Prop := ∀ (m : ℕ) (w : Fin m → ZMod 2 → Polynomial ℤ) (q : M6.Character.Vector m), M6.Character.localTransform w q = ∑ z : M6.Character.Vector m, Polynomial.C (M6.Character.character q z) * ∏ i, w i (z i)
#check target_6
def target_7 : Prop := ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (w : Fin m → ZMod 2 → Polynomial ℤ), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Character.weightedDual D w = M6.Character.weightedTransform D w
#check target_7
