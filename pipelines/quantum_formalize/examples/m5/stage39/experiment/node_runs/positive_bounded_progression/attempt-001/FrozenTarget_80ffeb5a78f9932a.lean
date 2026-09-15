import M5GlobalCriterionReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 < M5.ResidueCount.A w F → ∃ (S U : Finset ℕ) (N E : ℕ), 0 < E ∧ N < M5.birthBound w (M5.signaturePeriod F) ∧ ∀ j : ℕ, M5.PhysicalOrder.realizes (N + j * E) w F S U
