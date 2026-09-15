import FrozenTarget_40f66be21c2fe8a4
theorem M7.FinalSelector.empty_exact : QuantumHarnessFrozenTarget := by
  intro N w inst q hw hwN hq
  classical
  have hwin (x : M7.FinalSelector.Index N w q) :
      M7.FinalSelector.win q x = true ↔
        x ∈ M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) := by
    simpa only [M7.FinalSelector.win] using
      M7.StreamingIndices.stream_winners _ N q (M7.FinalSelector.family N w q) x
  have hex :
      (∃ x : M7.FinalSelector.Index N w q,
        M7.GlobalQuery.feasible q (M7.FinalSelector.family N w q) x) ↔
      ∃ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨M7.FinalSelector.realize q x,
        (M7.FinalSelector.index_feasible N w q hw hwN hq x).mp hx⟩
    · rintro ⟨c, hc⟩
      obtain ⟨x, hx⟩ := M7.FinalSelector.raw_realizable N w q hw hwN hq c hc
      refine ⟨x, (M7.FinalSelector.index_feasible N w q hw hwN hq x).mpr ?_⟩
      rw [hx]
      exact hc
  have hempty :
      (∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = false) ↔
      M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    constructor
    · intro h x hx
      have ht := (hwin x).mpr hx
      rw [h x] at ht
      cases ht
    · intro h x
      cases hb : M7.FinalSelector.win q x with
      | false => rfl
      | true => exact False.elim (h x ((hwin x).mp hb))
  exact hempty.trans
    ((M7.GlobalQuery.winners_exact _ N q (M7.FinalSelector.family N w q)).2.trans
      (not_congr hex))
