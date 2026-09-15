import M5PhysicalRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (q : List Bool), q ∈ M5.PhysicalRecovery.validWords N w F → q.length = M5.PhysicalRecovery.decisionCount N
