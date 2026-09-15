import FrozenTarget_cec7825692844890
theorem M5.ArithmeticWorkflow.birth_none : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0
  classical
  have hG := M5.GlobalCriterion.global_occurrence_criterion w F hw hF hF0
  constructor
  · intro hb
    by_contra hA
    have hpos : 0 < M5.ResidueCount.A w F := by omega
    obtain ⟨b, hb', _⟩ := M5.ArithmeticWorkflow.birth_exact w F hw hF hF0 hpos
    rw [hb] at hb'
    cases hb'
  · intro hA
    unfold M5.ArithmeticWorkflow.birth
    rw [M5.BirthSearch.birth_none_iff]
    intro N hbound hlower hd
    have hN : 0 < N := by omega
    apply le_of_not_gt
    intro hC
    obtain ⟨S, U, hR⟩ :=
      (M5.ArithmeticWorkflow.order_count_iff N w F hN (by omega) hF hF0).mp hC
    exact (hG.2.2.mp hA) ⟨N, S, U, hR⟩
