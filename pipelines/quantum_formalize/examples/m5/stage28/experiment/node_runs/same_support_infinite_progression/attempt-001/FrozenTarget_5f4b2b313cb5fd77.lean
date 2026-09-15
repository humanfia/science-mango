import M5FeasibleSource


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r s : Fin w → Fin T) (F : M5.BinaryPolynomial), 2 ≤ w → 0 < T → M5.BoundedConstruction.anchoredTuple r → M5.BoundedConstruction.anchoredTuple s → M5.BoundedConstruction.tupleSupportGcd r s = 1 → M5.completeSignature (M5.SupportPolynomial.ofResidueTuple r) (M5.SupportPolynomial.ofResidueTuple s) T = F → ∃ (A : Finset ℕ) (N E : ℕ), 0 < E ∧ N < M5.birthBound w T ∧ ∀ j : ℕ, M5.PhysicalOrder.realizes (N + j * E) w F A (M5.Packing.packedSupport s)
