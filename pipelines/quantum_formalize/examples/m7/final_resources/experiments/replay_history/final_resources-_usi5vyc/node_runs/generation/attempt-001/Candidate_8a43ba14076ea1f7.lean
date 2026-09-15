import FrozenTarget_8a43ba14076ea1f7
theorem M7.FinalResources.generation : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  have hcard := M7.CompactCorrectness.generate_card N w E hw hwN hE
  have hcount := M7.GenerationCalls.generate_count N w E
  simp_all only [M7.GeneratedFamily.size]
   all_goals grind
