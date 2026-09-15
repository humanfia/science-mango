import M5OriginalSpec

theorem M5.Final.global_birth_later : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → M5.Final.GlobalClause w F ∧ M5.Final.ProgressionClause w F ∧ M5.Final.BirthClause w F ∧ M5.Final.LaterClause w F := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → M5.Final.GlobalClause w F ∧ M5.Final.ProgressionClause w F ∧ M5.Final.BirthClause w F ∧ M5.Final.LaterClause w F
  intro w F hw hmon hconst
  refine ⟨M5.GlobalCriterion.global_occurrence_criterion w F hw hmon hconst,
    M5.GlobalCriterion.positive_bounded_progression w F hw hmon hconst, ?_,
    M5.ArithmeticWorkflow.later_exception w F hw hmon hconst⟩
  unfold M5.Final.BirthClause
  refine ⟨?_, M5.ArithmeticWorkflow.birth_none w F hw hmon hconst⟩
  intro hA
  obtain ⟨b, hbirth, hreal, hminimal⟩ :=
    M5.ArithmeticWorkflow.birth_exact w F hw hmon hconst hA
  obtain ⟨S, U, hSU⟩ := hreal
  have hreal : ∃ S U : Finset ℕ, M5.PhysicalOrder.realizes b w F S U := ⟨S, U, hSU⟩
  obtain ⟨hperiod, hwb, hdegree⟩ :=
    M5.OrderBoundary.signature_lower_bounds b w F S U hmon hconst hSU
  obtain ⟨S₀, U₀, N, E, hE, hN, hprogression⟩ :=
    M5.GlobalCriterion.positive_bounded_progression w F hw hmon hconst hA
  have hsource : M5.PhysicalOrder.realizes N w F S₀ U₀ := by
    simpa only [zero_mul, add_zero] using hprogression 0
  have hbN : b ≤ N := hminimal N ⟨S₀, U₀, hsource⟩
  have hwpos : 0 < w := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hw
  have hbpos : 0 < b := lt_of_lt_of_le hwpos hwb
  refine ⟨b, hbirth, le_trans hbN (Nat.le_of_lt hN),
    max_le hwb (Nat.succ_le_of_lt hdegree), hperiod, ?_, hreal, hminimal⟩
  exact (M5.ArithmeticWorkflow.order_count_iff b w F hbpos hwpos hmon hconst).2 hreal

theorem M5.Final.normalization : M5.Final.NormalizationClause := by
  change M5.Final.NormalizationClause
  unfold M5.Final.NormalizationClause
  exact M5.Translation.anchored_normalization

theorem M5.Final.period_and_order : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.PeriodClause F ∧ M5.Final.OrderClause w F ∧ M5.Final.LowerClause w F ∧ M5.Final.WeightOneClause F := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.PeriodClause F ∧ M5.Final.OrderClause w F ∧ M5.Final.LowerClause w F ∧ M5.Final.WeightOneClause F
  intro w F hw hF h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold M5.Final.PeriodClause
    obtain ⟨hp, hlaw⟩ := M5.Period.period_law F hF h0
    exact ⟨hp, M5.PeriodSearch.finite_search_eq_period F hF h0, hlaw, M5.PeriodSearch.finite_search_one⟩
  · unfold M5.Final.OrderClause
    intro N hN
    exact ⟨M5.ArithmeticWorkflow.order_count_nonnegative N w F hN hw hF h0,
      M5.ArithmeticWorkflow.order_count_iff N w F hN hw hF h0,
      M5.ArithmeticWorkflow.order_exception N w F hN hw hF h0,
      M5.OrderCount.exact_C N w F hN hw hF⟩
  · unfold M5.Final.LowerClause
    intro N S U hreal
    obtain ⟨hp, hwN, hdN⟩ := M5.OrderBoundary.signature_lower_bounds N w F S U hF h0 hreal
    exact ⟨hp, max_le hwN (Nat.succ_le_of_lt hdN)⟩
  · unfold M5.Final.WeightOneClause
    intro N S U
    exact M5.OrderBoundary.weight_one_iff N F S U
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OriginalM5Core w F
