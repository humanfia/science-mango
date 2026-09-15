import FrozenTarget_82e3a55b78ae122d
theorem M7.GenerationReplay.generate_checked : QuantumHarnessFrozenTarget := by
  classical
  intro N inst w E hE
  have hex := M7.CompactCorrectness.generate_exact N w E hE
  have hz : (M7.CompactGeneration.generate (N := N) w E).finalResidual = 0 := by
    tauto
  have hf : (M7.CompactGeneration.generate (N := N) w E).fuelExhausted = false := by
    tauto
  have hr : M7.GenerationReplay.replay w E ∅
      (M7.CompactGeneration.generate (N := N) w E).emitted =
      some (M7.CompactGeneration.generate (N := N) w E).finalBases := by
    unfold M7.CompactGeneration.generate
    apply M7.GenerationReplay.run_replay N w E ∅
    · rfl
    · exact hz
  simp [M7.GenerationReplay.check, hr, hz, hf]
