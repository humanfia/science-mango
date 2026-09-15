import M5PhysicalRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (p : List Bool), 0 < N → p.length ≤ M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.StateOK N p
