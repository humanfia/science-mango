import FrozenTarget_c468f9f2835d2033
theorem M7.GenerationReplay.run_replay : QuantumHarnessFrozenTarget := by
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero =>
      intro hroot hzero
      by_cases hpos : 0 < root
      · simp_all [M7.CompactGeneration.run, M7.GenerationReplay.replay,
          not_le_of_gt hpos]
      · simp_all [M7.CompactGeneration.run, M7.GenerationReplay.replay,
          le_of_not_gt hpos]
  | succ fuel ih =>
      intro hroot hzero
      by_cases hpos : 0 < root
      · have hstep : M7.GenerationReplay.stepPass w E bases
            (M7.CompactGeneration.emission w E bases) = true :=
          (M7.GenerationReplay.step_exact N w E bases _).2
            ⟨hroot ▸ hpos, rfl⟩
        simp only [M7.CompactGeneration.run, if_pos hpos,
          if_neg (not_le_of_gt hpos)] at hzero ⊢
        simp only [M7.GenerationReplay.replay, hstep, if_true]
        exact ih _ _ rfl hzero
      · have hstop := M7.CompactGeneration.stop N w E bases
          (fuel + 1) root (le_of_not_gt hpos)
        rw [hstop.1, hstop.2.1]
        have hres : M7.CompactGeneration.residual w E bases [] = 0 :=
          hroot.symm.trans (hstop.2.2.1.symm.trans hzero)
        simp [M7.GenerationReplay.replay, hres]
