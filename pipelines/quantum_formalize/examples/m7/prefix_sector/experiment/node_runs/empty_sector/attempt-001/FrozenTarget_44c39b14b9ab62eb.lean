import M7PrefixSector


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (A B WA WB : Finset ℕ), M7.PrefixSector.count N w ∅ A B WA WB = 0 ∧ M7.PrefixSector.completions N w ∅ A B WA WB = ∅
