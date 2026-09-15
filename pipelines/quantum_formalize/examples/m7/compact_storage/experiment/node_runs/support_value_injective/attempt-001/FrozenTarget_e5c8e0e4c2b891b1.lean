import M7CompactStorage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], Function.Injective (@M7.CompactStorage.supportBits N) ∧ Function.Injective (@M7.CompactStorage.valueBits N)
