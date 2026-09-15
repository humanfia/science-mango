import M6CharacterAccepted
import M6Normalization


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (q : M6.Character.Vector m), (q = 0 → M6.Character.localTransform (fun _ _ => (1 : Polynomial ℤ)) q = Polynomial.C ((2 : ℤ)^m)) ∧ (q ≠ 0 → M6.Character.localTransform (fun _ _ => (1 : Polynomial ℤ)) q = 0)
