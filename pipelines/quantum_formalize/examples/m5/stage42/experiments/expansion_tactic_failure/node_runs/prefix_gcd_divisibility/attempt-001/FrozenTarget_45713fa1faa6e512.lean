import M5ConditionalResidueCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T d : ℕ) (p q : List (Fin T)), (d ∣ M5.ConditionalResidueCount.selectedGcd T p q ↔ d ∣ T ∧ (∀ r ∈ p, d ∣ r.val) ∧ (∀ r ∈ q, d ∣ r.val))
