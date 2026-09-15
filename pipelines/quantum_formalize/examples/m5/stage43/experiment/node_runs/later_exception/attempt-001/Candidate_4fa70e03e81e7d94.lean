import FrozenTarget_4fa70e03e81e7d94
theorem M5.ArithmeticWorkflow.later_exception : QuantumHarnessFrozenTarget := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → ∀ b N : ℕ, M5.ArithmeticWorkflow.birth w F = some b → b ≤ N → ((¬ M5.signaturePeriod F ∣ N ∨ M5.OrderCount.C N w F = 0) ↔ ¬ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U))
  intro w F hw hF hF0 b N hb hbN
  classical
  by_cases hN : 0 < N
  · have he := M5.ArithmeticWorkflow.order_exception N w F hN (by omega) hF hF0
    constructor
    · rintro (hd | hz) ⟨S, U, hR⟩
      · exact hd (M5.OrderBoundary.signature_lower_bounds N w F S U hF hF0 hR).1
      · exact he.mp hz ⟨S, U, hR⟩
    · intro h
      exact Or.inr (he.mpr h)
  · have hz : M5.OrderCount.C N w F = 0 := by
      simp [M5.OrderCount.C, hN]
    constructor
    · intro _ h
      rcases h with ⟨S, U, hR⟩
      exact hN hR.1
    · intro _
      exact Or.inr hz
