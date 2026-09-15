import M5OrderBoundary


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), M5.PhysicalOrder.realizes N 1 F A B ↔ N = 1 ∧ F = 1 ∧ A = {0} ∧ B = {0}
