import M8BankLayout


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R S N slots : ℕ, R ≤ S → M6.Transfer.solveStorage R N slots ≤ M6.Transfer.solveStorage S N slots
