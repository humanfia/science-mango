import M7FinalResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → M7.CompactStorage.storedCoreBits N (M7.GeneratedFamily.size N w E) ≤ 16*(M7.GeneratedFamily.size N w E)*N ∧ M7.CompactStorage.storedWithTablesBits N (M7.GeneratedFamily.size N w E) ≤ 16*(M7.GeneratedFamily.size N w E)*N + 2*(M7.GeneratedFamily.size N w E)*Nat.totient N*N
