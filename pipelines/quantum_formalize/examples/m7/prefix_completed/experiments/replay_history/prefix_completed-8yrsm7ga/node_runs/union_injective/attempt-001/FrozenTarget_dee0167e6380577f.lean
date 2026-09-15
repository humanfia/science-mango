import M7PrefixCompleted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint A WA → Disjoint B WB → Set.InjOn (fun x : Finset ℕ × Finset ℕ => (A ∪ x.1, B ∪ x.2)) (M7.PrefixSector.completions N w E A B WA WB : Set (Finset ℕ × Finset ℕ))
