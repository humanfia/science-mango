import M5FiniteExclusion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), S.powerset.filter (fun H => ∀ p ∈ H, bad p = true) = (S.filter (fun p => bad p = true)).powerset
