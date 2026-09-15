import M5ArithmeticResidueRecovery
import M5ConditionalResidueCountAccepted
import M5PrefixPartitionAccepted
import M5ResidueRecoveryAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ {α : Type} (k : ℕ) (u : List α) (a : Fin (k - (u.take k).length) → α) (b : Fin (k - (u.drop k).length) → α), u.length ≤ 2*k → (M5.ArithmeticResidueRecovery.completionWord k u a b).length = 2*k ∧ u.IsPrefix (M5.ArithmeticResidueRecovery.completionWord k u a b) ∧ (M5.ArithmeticResidueRecovery.completionWord k u a b).take k = u.take k ++ List.ofFn a ∧ (M5.ArithmeticResidueRecovery.completionWord k u a b).drop k = u.drop k ++ List.ofFn b
