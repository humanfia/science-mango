import M7CompactStorage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N H : ℕ) [NeZero N], M7.CompactStorage.coreBits N = 12*N+4 ∧ M7.CompactStorage.coreBits N ≤ 16*N ∧ M7.CompactStorage.tableBits N = Nat.totient N*(N+1) ∧ M7.CompactStorage.storedCoreBits N H ≤ 16*H*N ∧ M7.CompactStorage.storedWithTablesBits N H ≤ 16*H*N + 2*H*Nat.totient N*N
