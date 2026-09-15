import M5ArithmeticResidueRecovery
import M5ConditionalResidueCountAccepted
import M5PrefixPartitionAccepted
import M5ResidueRecoveryAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T k : ℕ) (p : List (Fin T)) (a : Fin k → Fin T), M5.ConditionalResidueCount.selectedPolynomial (p ++ List.ofFn a) = M5.ConditionalResidueCount.completedPolynomial (M5.ConditionalResidueCount.selectedPolynomial p) a ∧ M5.ConditionalResidueCount.prefixGcd (p ++ List.ofFn a) = Nat.gcd (M5.ConditionalResidueCount.prefixGcd p) (Finset.univ.gcd (fun i : Fin k => (a i).val))
