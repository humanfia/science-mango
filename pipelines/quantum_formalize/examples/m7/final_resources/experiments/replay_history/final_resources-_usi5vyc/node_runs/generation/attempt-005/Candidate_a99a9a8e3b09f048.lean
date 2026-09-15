import FrozenTarget_a99a9a8e3b09f048
theorem M7.FinalResources.generation : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  have hcard : (M7.CompactGeneration.generate (N := N) w E).finalBases.card = M7.GeneratedFamily.size N w E := by
    simpa [M7.GeneratedFamily.size] using (M7.CompactCorrectness.generate_card N w E hw hwN hE)
  have hcount := M7.GenerationCalls.generate_count N w E
  refine ⟨hcard, ?_⟩
  simpa only [hcard, M7.GeneratedFamily.size] using hcount.2
