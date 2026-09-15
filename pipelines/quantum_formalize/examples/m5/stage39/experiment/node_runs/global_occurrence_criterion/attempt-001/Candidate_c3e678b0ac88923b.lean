import FrozenTarget_c3e678b0ac88923b
theorem M5.GlobalCriterion.global_occurrence_criterion : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro w F hw hF hF0
  have hwpos : 0 < w := by omega
  have hnonneg := (M5.ResidueCount.period_A_exact w F hwpos hF hF0).2.1
  have hiff : 0 < M5.ResidueCount.A w F ↔ ∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U := by
    constructor
    · intro hA
      obtain ⟨S, U, N, E, hE, hN, hprogress⟩ :=
        M5.GlobalCriterion.positive_bounded_progression w F hw hF hF0 hA
      refine ⟨N, S, U, ?_⟩
      simpa only [Nat.zero_mul, Nat.add_zero] using hprogress 0
    · rintro ⟨N, S, U, hphys⟩
      exact M5.GlobalCriterion.physical_implies_A_positive N w F S U hwpos hF hF0 hphys
  refine ⟨hnonneg, hiff, ?_⟩
  constructor
  · intro hzero hexists
    have hpos := hiff.mpr hexists
    omega
  · intro hnone
    have hnotpos : ¬ 0 < M5.ResidueCount.A w F := fun hpos => hnone (hiff.mp hpos)
    omega
