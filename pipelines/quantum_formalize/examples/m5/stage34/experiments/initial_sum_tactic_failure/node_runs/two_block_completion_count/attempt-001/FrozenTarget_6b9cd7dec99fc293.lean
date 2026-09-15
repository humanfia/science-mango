import M5ConditionalCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (A B WA WB : Finset ℕ) (kA kB : ℕ), P.Monic → Disjoint A WA → Disjoint B WB → M5.ConditionalCount.nSelected P A WA kA * M5.ConditionalCount.nSelected P B WB kB = M5.ConditionalCount.twoBlockIndicatorSum P A B WA WB kA kB
