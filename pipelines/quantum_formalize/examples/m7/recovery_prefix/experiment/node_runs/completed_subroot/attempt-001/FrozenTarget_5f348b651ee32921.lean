import M7PrefixBitsAccepted
import M7RecoveryPrefix
import M7ResiduePrefixAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), M7.RecoveryPrefix.completed N w E p ⊆ M7.RecoveryPrefix.completed N w E []
