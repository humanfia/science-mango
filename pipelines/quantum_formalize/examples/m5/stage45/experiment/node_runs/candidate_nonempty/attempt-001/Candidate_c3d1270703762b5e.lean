import FrozenTarget_c3d1270703762b5e
theorem M5.PeriodSearch.candidate_nonempty : QuantumHarnessFrozenTarget := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → (M5.PeriodSearch.candidates F).Nonempty
  intro F hmonic hcoeff
  classical
  obtain ⟨hpos, hlaw⟩ := M5.Period.period_law F hmonic hcoeff
  have hbound := M5.Period.period_cardinality_bound F hmonic hcoeff
  have hdiv : F ∣ M5.cyclicModulus (M5.signaturePeriod F) :=
    (hlaw _).mpr (dvd_refl _)
  refine ⟨M5.signaturePeriod F, ?_⟩
  simp [M5.PeriodSearch.candidates, hdiv, hpos, hbound, Nat.succ_le_iff, Nat.lt_succ_iff]
