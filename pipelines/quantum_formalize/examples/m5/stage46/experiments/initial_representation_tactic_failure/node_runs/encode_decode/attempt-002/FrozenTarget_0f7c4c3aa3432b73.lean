import M5PhysicalRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (q : List Bool), 0 < N → q.length = M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) = q
