import M5PhysicalRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → A ⊆ Finset.range N → B ⊆ Finset.range N → 0 ∈ A → 0 ∈ B → (M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N A B) = A ∧ M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N A B) = B)
