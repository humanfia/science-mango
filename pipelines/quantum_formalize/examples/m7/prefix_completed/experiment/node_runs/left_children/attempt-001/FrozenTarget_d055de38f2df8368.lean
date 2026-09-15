import M7PrefixCompleted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), ∀ i ∈ WA, M7.PrefixCompleted.Base N A B WA WB → M7.PrefixCompleted.Base N A B (WA.erase i) WB ∧ M7.PrefixCompleted.Base N (insert i A) B (WA.erase i) WB
