import FrozenTarget
theorem QuantumHarnessExample.nat_add_comm : QuantumHarnessFrozenTarget := by
  change ∀ a b : Nat, a + b = b + a
  intro a b
  exact Nat.add_comm a b
