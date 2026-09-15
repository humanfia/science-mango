import M7PrefixCompleted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), ∀ i ∈ WB, M7.PrefixCompleted.Base N A B WA WB → M7.PrefixCompleted.Base N A B WA (WB.erase i) ∧ M7.PrefixCompleted.Base N A (insert i B) WA (WB.erase i)
