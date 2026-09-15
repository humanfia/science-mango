import FrozenTarget_c48610d5448f3758
theorem M7.FinalResources.generation : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  have hcard := M7.CompactCorrectness.generate_card N w E hw hwN hE
  have hcount := M7.GenerationCalls.generate_count N w E
  unfold M7.GeneratedFamily.size
  refine ⟨hcard, hcount.2.1, ?_⟩
  simpa only [hcard] using hcount.2.2
