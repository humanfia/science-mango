import M5GlobalCriterion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (F : M5.BinaryPolynomial) (r s : Fin w → Fin T), 0 < w → 0 < T → M5.BoundedConstruction.anchoredTuple r → M5.BoundedConstruction.anchoredTuple s → M5.BoundedConstruction.tupleSupportGcd r s = 1 → M5.completeSignature (M5.SupportPolynomial.ofResidueTuple r) (M5.SupportPolynomial.ofResidueTuple s) T = F → ∃ a b : Fin (w-1) → Fin T, M5.ResidueCount.feasible F a b
