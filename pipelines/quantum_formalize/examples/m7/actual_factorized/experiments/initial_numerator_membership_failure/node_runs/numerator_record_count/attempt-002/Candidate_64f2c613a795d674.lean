import FrozenTarget_64f2c613a795d674
theorem M7.ActualFactorized.numerator_record_count : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ (sector : M7.ActualFactorized.Outer N → Prop) (L R : Finset (ZMod N) → Prop), M7.ActualFactorized.numerator c sector L R = M7.ActualFactorized.recordCount c sector L R
  intro N inst c sector L R
  classical
  unfold M7.ActualFactorized.numerator M7.ActualFactorized.recordCount
  rw [M7.Factorized.numerator_record_card]
  refine Finset.card_bij (fun a _ => M7.ActualFactorized.toRecord a) ?_ ?_ ?_
  · rintro ⟨⟨u, e⟩, s, t⟩ ha
    cases e <;> simpa [M7.Factorized.records, M7.ActualFactorized.toRecord, M7.ActualFactorized.leftImage, M7.ActualFactorized.rightImage, M7.Action.act, Finset.mem_filter, Finset.mem_univ] using ha
  · intro a ha b hb h
    exact (M7.ActualFactorized.record_coordinates N).1 h
  · intro g hg
    obtain ⟨a, rfl⟩ := (M7.ActualFactorized.record_coordinates N).2 g
    refine ⟨a, ?_, rfl⟩
    rcases a with ⟨⟨u, e⟩, s, t⟩
    cases e <;> simpa [M7.Factorized.records, M7.ActualFactorized.toRecord, M7.ActualFactorized.leftImage, M7.ActualFactorized.rightImage, M7.Action.act, Finset.mem_filter, Finset.mem_univ] using hg
