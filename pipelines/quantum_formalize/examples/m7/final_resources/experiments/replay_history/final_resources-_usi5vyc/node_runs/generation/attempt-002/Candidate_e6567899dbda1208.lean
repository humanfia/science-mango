import FrozenTarget_e6567899dbda1208
theorem M7.FinalResources.generation : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  have hcard := M7.CompactCorrectness.generate_card N w E hE
  have hcount := M7.GenerationCalls.generate_count N w E
  simp only [M7.GeneratedFamily.size] at *
  g rind
