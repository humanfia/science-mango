import M5PhysicalOrder

noncomputable def preflight_period_control : Prop :=
  ∀ (A B : Finset ℕ) (w T : ℕ), 2 ≤ w → 0 < T → 0 ∈ A → 0 ∈ B → (∀ b ∈ B, b < w * T) → 0 < M5.PhysicalOrder.supportPeriod A B ∧ M5.PhysicalOrder.supportPeriod A B ≤ 2 ^ (w * T) ∧ EuclideanDomain.gcd (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) ∣ M5.cyclicModulus (M5.PhysicalOrder.supportPeriod A B)

noncomputable def preflight_literal_progression : Prop :=
  ∀ (A B : Finset ℕ) (w T : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → 0 < T → A.card = w → B.card = w → 0 ∈ A → 0 ∈ B → (∀ a ∈ A, a < M5.packingCutoff w T) → (∀ b ∈ B, b < w * T) → M5.RepairSupport.combinedGcd A B = 1 → M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) T = F → ∀ j : ℕ, M5.packingCutoff w T ≤ T + j * M5.PhysicalOrder.supportPeriod A B → M5.PhysicalOrder.realizes (T + j * M5.PhysicalOrder.supportPeriod A B) w F A B

noncomputable def preflight_bounded_order : Prop :=
  ∀ (A B : Finset ℕ) (w T : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → 0 < T → A.card = w → B.card = w → 0 ∈ A → 0 ∈ B → (∀ a ∈ A, a < M5.packingCutoff w T) → (∀ b ∈ B, b < w * T) → M5.RepairSupport.combinedGcd A B = 1 → M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) T = F → ∃ N : ℕ, N < M5.birthBound w T ∧ M5.PhysicalOrder.realizes N w F A B
