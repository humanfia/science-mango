import FrozenTarget_1098225a9ae47689
theorem M7.Domain.support_gcd : QuantumHarnessFrozenTarget := by
  intro N inst A B
  unfold M7.Domain.connectivityGcd
  rw [M7.Supports.support N A, M7.Supports.support N B]
