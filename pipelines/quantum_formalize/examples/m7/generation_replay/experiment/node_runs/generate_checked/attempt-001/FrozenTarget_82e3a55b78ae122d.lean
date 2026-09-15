import M7GenerationReplay

theorem M7.GenerationReplay.step_exact : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (e : M7.CompactGeneration.Emission N), M7.GenerationReplay.stepPass w E bases e = true ↔ 0 < M7.CompactGeneration.residual w E bases [] ∧ e = M7.CompactGeneration.emission w E bases := by
  classical
  intro N inst w E bases e
  change M7.GenerationReplay.stepPass w E bases e = true ↔ _
  constructor
  · intro h
    simp only [M7.GenerationReplay.stepPass, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hpos, hcheck⟩, hdepth, hleaf, hrep, haction, hleafSig, hrepSig, hstab⟩
    have hpath := M7.DescentTrace.check_unique
      (M7.CompactGeneration.residual w E bases) [] e.path hcheck
    rw [hdepth] at hpath
    refine ⟨hpos, ?_⟩
    cases e
    dsimp only at *
    simp_all [M7.CompactGeneration.emission, M7.DescentTrace.endpoint_recover]
  · rintro ⟨hpos, rfl⟩
    simp [M7.GenerationReplay.stepPass, M7.CompactGeneration.emission,
      M7.DescentTrace.trace_length, M7.DescentTrace.check_trace,
      M7.DescentTrace.endpoint_recover, hpos]

theorem M7.GenerationReplay.run_replay : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), root = M7.CompactGeneration.residual w E bases [] → (M7.CompactGeneration.run w E fuel bases root).finalResidual = 0 → M7.GenerationReplay.replay w E bases (M7.CompactGeneration.run w E fuel bases root).emitted = some (M7.CompactGeneration.run w E fuel bases root).finalBases := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → M7.GenerationReplay.check w E (M7.CompactGeneration.generate (N := N) w E) = true
