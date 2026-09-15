import FrozenTarget_c79a0ed8f603996a
theorem M7.Domain.support_gcd : QuantumHarnessFrozenTarget := by
  intro N inst A B
  unfold M7.Domain.connectivityGcd
  rw [M7.Supports.support N A, M7.Supports.support N B]
