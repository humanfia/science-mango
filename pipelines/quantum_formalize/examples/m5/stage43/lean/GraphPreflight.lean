import M5ArithmeticWorkflowReady
example : Prop := (∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F.coeff 0 = 1 → (0 < M5.OrderCount.C N w F ↔ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)))
example : Prop := (∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F.coeff 0 = 1 → 0 ≤ M5.OrderCount.C N w F)
example : Prop := (∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F.coeff 0 = 1 → (M5.OrderCount.C N w F = 0 ↔ ¬ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)))
example : Prop := (∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 < M5.ResidueCount.A w F → ∃ b : ℕ, M5.ArithmeticWorkflow.birth w F = some b ∧ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes b w F S U) ∧ ∀ N : ℕ, (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U) → b ≤ N)
example : Prop := (∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → (M5.ArithmeticWorkflow.birth w F = none ↔ M5.ResidueCount.A w F = 0))
example : Prop := (∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → ∀ b N : ℕ, M5.ArithmeticWorkflow.birth w F = some b → b ≤ N → ((¬ M5.signaturePeriod F ∣ N ∨ M5.OrderCount.C N w F = 0) ↔ ¬ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)))
