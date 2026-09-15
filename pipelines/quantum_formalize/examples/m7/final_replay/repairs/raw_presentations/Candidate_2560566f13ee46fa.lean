import FrozenTarget_2560566f13ee46fa
theorem M7.FinalReplay.raw_presentations : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q hw hwN c hc y
  have hv := ((M7.FinalReplay.parts N w q c).mp hc).1
  have hsets := (M7.FinalReplay.checked_sets N w q hw hwN c hc).2
  rw [hsets]
  have h := M7.FinalSelector.presentation_exact N w q hw hwN hv y
  have hp : ∀ x : M7.FinalSelector.Index N w q,
      M7.FinalSelector.present q x = true ↔
        M7.GlobalQuery.present q (M7.FinalSelector.family N w q) x := by
    intro x
    unfold M7.FinalSelector.present
    rw [Bool.and_eq_true, decide_eq_true_eq]
    rw [M7.FinalSelector.win, M7.StreamingIndices.stream_winners]
    rfl
  simpa only [hp, M7.QueryCertificate.allPresentations,
    Finset.mem_filter, Finset.mem_univ, true_and] using h
