import M5PeriodSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → (M5.PeriodSearch.candidates F).Nonempty
