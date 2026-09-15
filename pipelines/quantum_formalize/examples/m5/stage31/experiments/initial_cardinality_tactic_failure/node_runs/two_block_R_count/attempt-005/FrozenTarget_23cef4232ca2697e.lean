import M5ResidueCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (T d k : ℕ), P.Monic → 0 < T → d ∣ T → M5.ResidueCount.ROne P T d k ^ 2 = ∑ a : Fin k → Fin T, ∑ b : Fin k → Fin T, (@ite ℤ (((∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial a) ∧ ((∀ i : Fin k, d ∣ (b i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial b)) (Classical.propDecidable _) 1 0)
