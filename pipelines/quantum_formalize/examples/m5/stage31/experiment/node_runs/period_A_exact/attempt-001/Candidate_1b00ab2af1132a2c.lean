import FrozenTarget_1b00ab2af1132a2c
theorem M5.ResidueCount.period_A_exact : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0
  obtain ⟨hT, hperiod⟩ := M5.Period.period_law F hF hF0
  have hFT : F ∣ M5.cyclicModulus (M5.signaturePeriod F) :=
    (hperiod (M5.signaturePeriod F)).2 (dvd_refl _)
  unfold M5.ResidueCount.A
  exact ⟨M5.ResidueCount.exact_rawA (M5.signaturePeriod F) w F hT hw hF hFT,
    M5.ResidueCount.rawA_nonnegative_and_positive (M5.signaturePeriod F) w F hT hw hF hFT⟩
