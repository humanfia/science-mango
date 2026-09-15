import FrozenTarget_b0b3a24865c75a14
theorem M7.FinalSelector.presentation_exact : QuantumHarnessFrozenTarget := by
  intro N w inst q hw hwN hq c
  classical
  have hp : ∀ x : M7.FinalSelector.Index N w q,
      M7.FinalSelector.present q x = true ↔
        M7.GlobalQuery.present q (M7.FinalSelector.family N w q) x := by
    intro x
    unfold M7.FinalSelector.present
    rw [Bool.and_eq_true, decide_eq_true_eq]
    rw [M7.FinalSelector.win, M7.StreamingIndices.stream_winners]
    rfl
  have hs : M7.GlobalQuery.separated (M7.FinalSelector.family N w q) :=
    M7.GeneratedFamily.family_separated N w (M7.QuerySectors.effective N q)
      hw hwN (M7.QuerySectors.effective_valid N q hq)
  constructor
  · intro hc
    obtain ⟨x, hx, hxc⟩ := (M7.FinalSelector.raw_output N w q hw hwN hq c).mp hc
    have hxw : x ∈ M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) := by
      simpa only [M7.FinalSelector.win, M7.StreamingIndices.stream_winners] using hx
    have hxc' : M7.GlobalQuery.realize (M7.FinalSelector.family N w q) x = c := hxc
    obtain ⟨y, hy, hu⟩ := M7.GlobalQuery.physical_presentation _ N q
      (M7.FinalSelector.family N w q) hs x hxw
    refine ⟨y, ⟨(hp y).mpr hy.1, hy.2.trans hxc'⟩, ?_⟩
    intro z hz
    apply hu z
    exact ⟨(hp z).mp hz.1, hz.2.trans hxc'.symm⟩
  · rintro ⟨x, hx, _⟩
    have hxw := (M7.GlobalQuery.presentation_sound _ N q
      (M7.FinalSelector.family N w q) x ((hp x).mp hx.1)).1
    have hxwin : M7.FinalSelector.win q x = true := by
      simpa only [M7.FinalSelector.win, M7.StreamingIndices.stream_winners] using hxw
    have hc := (M7.FinalSelector.winner_exact N w q hw hwN hq x).mp hxwin
    rw [hx.2] at hc
    exact hc
