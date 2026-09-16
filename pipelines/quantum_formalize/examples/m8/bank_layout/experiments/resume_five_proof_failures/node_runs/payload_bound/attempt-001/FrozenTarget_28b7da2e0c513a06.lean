import M8BankLayout


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M8.BankLayout.payloadSlots N ≤ 20000*(N+1)^3
