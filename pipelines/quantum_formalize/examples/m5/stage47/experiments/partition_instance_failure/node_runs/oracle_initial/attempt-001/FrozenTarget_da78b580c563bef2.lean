import M5ArithmeticResidueRecovery
import M5ConditionalResidueCountAccepted
import M5PrefixPartitionAccepted
import M5ResidueRecoveryAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), M5.ArithmeticResidueRecovery.oracle w F [] = M5.ResidueCount.A w F
