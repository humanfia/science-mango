import FrozenTarget_3a4cedab35e076d6
theorem M7.GenerationReplay.checked_coverage : QuantumHarnessFrozenTarget := by
  classical
  intro N inst w E hE hw o hc
  have hr : M7.GenerationReplay.replay w E ∅ o.emitted = some o.finalBases := by
    cases he : M7.GenerationReplay.replay w E ∅ o.emitted with
    | none => simp [M7.GenerationReplay.check, he] at hc
    | some bases =>
        have hh : bases = o.finalBases ∧ o.finalResidual = 0 ∧ o.fuelExhausted = false := by
          simpa only [M7.GenerationReplay.check, he, decide_eq_true_eq] using hc
        exact he.trans (congrArg some hh.1)
  obtain ⟨hg, hf⟩ := M7.GenerationReplay.replay_sound N w E hE ∅ o.finalBases o.emitted
    (M7.CompactCorrectness.initial N w E hE).1 hr
  have hz := (M7.GenerationReplay.replay_terminal_fold N w E ∅ o.finalBases o.emitted hr).1
  have hzero : M7.RecoveryInstance.count w E o.finalBases [] = 0 := by
    simpa only [M7.CompactCorrectness.residual_eq] using hz
  refine ⟨hg, hf, (M7.GenerationReplay.fresh_nodup N w E ∅ o.emitted hf).1, ?_, ?_⟩
  · exact (M7.RecoveryInstance.root_zero N w E o.finalBases hE hg).mp hzero
  · have hcard := (M7.RecoveryInstance.count_card N w E o.finalBases hE hg []).2.1
    have hempty : M7.RecoveryInstance.remaining w E o.finalBases [] = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa only [hzero, Int.toNat_zero] using hcard.symm
    apply M7.RawCoverage.remaining_coverage N w E o.finalBases hw
    · first | exact hg.1 | exact hg.2
    · first | exact hg.2 | exact hg.1
    · exact hempty
