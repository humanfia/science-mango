import FrozenTarget_5a8ab7c86d8e3c3a
theorem M5.ConditionalResidueCount.period_conditionalA_exact : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin (M5.signaturePeriod F))), _
  intro w F p q hw hF hF0
  have hperiod := M5.Period.period_law F hF hF0
  have hdiv : F ∣ M5.cyclicModulus (M5.signaturePeriod F) :=
    (hperiod.2 (M5.signaturePeriod F)).2 (dvd_refl _)
  have he : M5.ConditionalResidueCount.conditionalA w F p q =
      (M5.ConditionalResidueCount.validCompletions (M5.signaturePeriod F) w F p q).card := by
    simpa only [M5.ConditionalResidueCount.conditionalA] using
      M5.ConditionalResidueCount.exact_conditionalA
        (M5.signaturePeriod F) w F p q hperiod.1 hw hF hdiv
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    exact Int.natCast_nonneg _
  · rw [he, Int.natCast_pos, Finset.card_pos]
    by_cases hf : M5.ConditionalResidueCount.fits w p q
    <;> simp [M5.ConditionalResidueCount.validCompletions, hf,
      Finset.Nonempty, Prod.exists]
