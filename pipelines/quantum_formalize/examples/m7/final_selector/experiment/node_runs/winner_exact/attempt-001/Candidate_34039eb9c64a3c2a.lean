import FrozenTarget_34039eb9c64a3c2a
theorem M7.FinalSelector.winner_exact : QuantumHarnessFrozenTarget := by
  intro N w inst q hw hwN hq x
  rw [M7.FinalSelector.win, M7.StreamingIndices.stream_winners]
  rw [(M7.GlobalQuery.winners_exact _ N q (M7.FinalSelector.family N w q)).1 x]
  unfold M7.FinalSelector.RawWinner
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨(M7.FinalSelector.index_feasible N w q hw hwN hq x).mp hx, ?_⟩
    intro c hc
    obtain ⟨y, hy⟩ := M7.FinalSelector.raw_realizable N w q hw hwN hq c hc
    have hf := (M7.FinalSelector.index_feasible N w q hw hwN hq y).mpr (hy ▸ hc)
    have hm := hmin y hf
    rw [← hy]
    simpa only [M7.GlobalQuery.objective, M7.FinalSelector.realize,
      M7.GlobalQuery.realize, M7.Action.act_identity] using hm
  · rintro ⟨hx, hmin⟩
    refine ⟨(M7.FinalSelector.index_feasible N w q hw hwN hq x).mpr hx, ?_⟩
    intro y hy
    have hm := hmin (M7.FinalSelector.realize q y)
      ((M7.FinalSelector.index_feasible N w q hw hwN hq y).mp hy)
    simpa only [M7.GlobalQuery.objective, M7.FinalSelector.realize,
      M7.GlobalQuery.realize, M7.Action.act_identity] using hm
