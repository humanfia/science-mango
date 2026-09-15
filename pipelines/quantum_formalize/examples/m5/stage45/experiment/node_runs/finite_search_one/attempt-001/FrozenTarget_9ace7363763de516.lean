import M5PeriodSearch

theorem M5.PeriodSearch.candidate_nonempty : ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → (M5.PeriodSearch.candidates F).Nonempty := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → (M5.PeriodSearch.candidates F).Nonempty
  intro F hmonic hcoeff
  classical
  obtain ⟨hpos, hlaw⟩ := M5.Period.period_law F hmonic hcoeff
  have hbound := M5.Period.period_cardinality_bound F hmonic hcoeff
  have hdiv : F ∣ M5.cyclicModulus (M5.signaturePeriod F) :=
    (hlaw _).mpr (dvd_refl _)
  refine ⟨M5.signaturePeriod F, ?_⟩
  simp [M5.PeriodSearch.candidates, hdiv, hpos, hbound, Nat.succ_le_iff, Nat.lt_succ_iff]

theorem M5.PeriodSearch.finite_search_member : ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.PeriodSearch.finiteSearch F ∈ M5.PeriodSearch.candidates F := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.PeriodSearch.finiteSearch F ∈ M5.PeriodSearch.candidates F
  intro F hmonic hcoeff
  classical
  have h := M5.PeriodSearch.candidate_nonempty F hmonic hcoeff
  simp only [M5.PeriodSearch.finiteSearch, dif_pos h]
  exact Finset.min'_mem _ _

theorem M5.PeriodSearch.finite_search_eq_period : ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.PeriodSearch.finiteSearch F = M5.signaturePeriod F := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.PeriodSearch.finiteSearch F = M5.signaturePeriod F
  intro F hmonic hcoeff
  classical
  obtain ⟨hpos, hlaw⟩ := M5.Period.period_law F hmonic hcoeff
  have hbound := M5.Period.period_cardinality_bound F hmonic hcoeff
  have hdiv : F ∣ M5.cyclicModulus (M5.signaturePeriod F) :=
    (hlaw _).mpr (dvd_refl _)
  have ht : M5.signaturePeriod F ∈ M5.PeriodSearch.candidates F := by
    simp [M5.PeriodSearch.candidates, hdiv, hpos, hbound, Nat.succ_le_iff, Nat.lt_succ_iff]
  have hs := M5.PeriodSearch.finite_search_member F hmonic hcoeff
  have hsprops : 0 < M5.PeriodSearch.finiteSearch F ∧
      F ∣ M5.cyclicModulus (M5.PeriodSearch.finiteSearch F) := by
    simp [M5.PeriodSearch.candidates] at hs
    constructor
    · omega
    · aesop
  apply Nat.le_antisymm
  · have hn := M5.PeriodSearch.candidate_nonempty F hmonic hcoeff
    simp only [M5.PeriodSearch.finiteSearch, dif_pos hn]
    exact Finset.min'_le _ _ ht
  · exact Nat.le_of_dvd hsprops.1 ((hlaw _).mp hsprops.2)
def QuantumHarnessFrozenTarget : Prop :=
  M5.PeriodSearch.finiteSearch (1 : M5.BinaryPolynomial) = 1
