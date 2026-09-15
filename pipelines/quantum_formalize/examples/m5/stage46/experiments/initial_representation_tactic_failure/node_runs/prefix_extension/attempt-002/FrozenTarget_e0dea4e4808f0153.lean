import M5PhysicalRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (p q : List Bool), 0 < N → p.length ≤ M5.PhysicalRecovery.decisionCount N → q.length = M5.PhysicalRecovery.decisionCount N → (p.IsPrefix q ↔ M5.PhysicalRecovery.selectedA N p ⊆ M5.PhysicalRecovery.selectedA N q ∧ M5.PhysicalRecovery.selectedA N q ⊆ M5.PhysicalRecovery.selectedA N p ∪ M5.PhysicalRecovery.availableA N p ∧ M5.PhysicalRecovery.selectedB N p ⊆ M5.PhysicalRecovery.selectedB N q ∧ M5.PhysicalRecovery.selectedB N q ⊆ M5.PhysicalRecovery.selectedB N p ∪ M5.PhysicalRecovery.availableB N p)
