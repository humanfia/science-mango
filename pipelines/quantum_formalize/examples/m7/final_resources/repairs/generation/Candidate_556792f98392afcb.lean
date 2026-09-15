import FrozenTarget_556792f98392afcb
theorem M7.FinalResources.generation : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  dsimp only [M7.GeneratedFamily.size]
  have hc := M7.CompactCorrectness.generate_card N w E hE
  obtain ⟨_, hcount, horbits⟩ := M7.GenerationCalls.generate_count N w E
  refine ⟨hc, hcount, ?_⟩
  simpa only [hc] using horbits
