import FrozenTarget_68f3f52a14f74a70
theorem M7.FinalResources.generation : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  have hcard : (M7.CompactGeneration.generate (N := N) w E).finalBases.card = M7.GeneratedFamily.size N w E := by
    unfold M7.GeneratedFamily.size
    apply M7.CompactCorrectness.generate_card <;> assumption
  have hcount := M7.GenerationCalls.generate_count N w E
  repeat' match goal with
    | h : _ ∧ _ ⊢ _ => rcases h with ⟨h₁, h₂⟩
  refine ⟨hcard, ?_, ?_⟩
  all_goals
    simp_all only [M7.GeneratedFamily.size]
    <;> nlinarith
