import FrozenTarget_683ea1edec0b9ef5
theorem M7.ActualFactorized.numerator_record_count : QuantumHarnessFrozenTarget := by
  intro N inst c sector L R
  classical
  unfold M7.ActualFactorized.numerator M7.ActualFactorized.recordCount
  rw [M7.Factorized.numerator_record_card]
  refine Finset.card_bij (fun a _ => M7.ActualFactorized.toRecord a) ?_ ?_ ?_
  · rintro ⟨⟨u, e⟩, s, t⟩ ha
    simp only [M7.Factorized.records, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a ha b hb hab
    exact (M7.ActualFactorized.record_coordinates N).1 hab
  · intro g hg
    refine ⟨M7.ActualFactorized.fromRecord g, ?_, ?_⟩
    · simp only [M7.Factorized.records, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hg
    · cases g
      rfl
