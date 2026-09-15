import FrozenTarget_db2057ba95e85a9f
theorem M7.FinalSelector.empty_exact : QuantumHarnessFrozenTarget := by
  intro N w inst q hw hwN hq
  classical
  have hempty :
      (∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = false) ↔
        M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) = ∅ := by
    constructor
    · intro h
      apply Finset.ext
      intro x
      simp only [Finset.mem_empty, iff_false]
      intro hx
      have ht := (M7.StreamingIndices.stream_winners _ N q
        (M7.FinalSelector.family N w q) x).mpr hx
      change M7.FinalSelector.win q x = true at ht
      rw [h x] at ht
      cases ht
    · intro h x
      cases hx : M7.FinalSelector.win q x with
      | false => rfl
      | true =>
        exfalso
        have ht : M7.StreamingIndices.streamWin q
            (M7.FinalSelector.family N w q) x = true := hx
        have hm := (M7.StreamingIndices.stream_winners _ N q
          (M7.FinalSelector.family N w q) x).mp ht
        rw [h] at hm
        exact Finset.not_mem_empty x hm
  rw [hempty, (M7.GlobalQuery.winners_exact _ N q
    (M7.FinalSelector.family N w q)).2]
  constructor
  · intro h ⟨c, hc⟩
    obtain ⟨x, hx⟩ := M7.FinalSelector.raw_realizable N w q hw hwN hq c hc
    apply h
    refine ⟨x, (M7.FinalSelector.index_feasible N w q hw hwN hq x).mpr ?_⟩
    rw [hx]
    exact hc
  · intro h ⟨x, hx⟩
    exact h ⟨M7.FinalSelector.realize q x,
      (M7.FinalSelector.index_feasible N w q hw hwN hq x).mp hx⟩
