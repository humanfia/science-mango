import M5GlobalCriterionReady
#check (∀ (N w : ℕ) (F : M5.BinaryPolynomial) (S U : Finset ℕ), 0 < w → F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F S U → 0 < M5.ResidueCount.A w F)
#check (∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 < M5.ResidueCount.A w F → ∃ (S U : Finset ℕ) (N E : ℕ), 0 < E ∧ N < M5.birthBound w (M5.signaturePeriod F) ∧ ∀ j : ℕ, M5.PhysicalOrder.realizes (N + j * E) w F S U)
#check (∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 ≤ M5.ResidueCount.A w F ∧ (0 < M5.ResidueCount.A w F ↔ ∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U) ∧ (M5.ResidueCount.A w F = 0 ↔ ¬ (∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U)))
