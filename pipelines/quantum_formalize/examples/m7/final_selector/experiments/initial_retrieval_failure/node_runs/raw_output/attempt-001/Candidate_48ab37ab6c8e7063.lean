import FrozenTarget_48ab37ab6c8e7063
theorem M7.FinalSelector.raw_output : QuantumHarnessFrozenTarget := by
  intro N w inst q hw hwN hq c
  constructor
  · intro hc
    obtain ⟨x, hx⟩ := M7.FinalSelector.raw_realizable N w q hw hwN hq c hc.1
    refine ⟨x, ?_, hx⟩
    apply (M7.FinalSelector.winner_exact N w q hw hwN hq x).mpr
    rw [hx]
    exact hc
  · rintro ⟨x, hx, hxc⟩
    have hc := (M7.FinalSelector.winner_exact N w q hw hwN hq x).mp hx
    rw [hxc] at hc
    exact hc
