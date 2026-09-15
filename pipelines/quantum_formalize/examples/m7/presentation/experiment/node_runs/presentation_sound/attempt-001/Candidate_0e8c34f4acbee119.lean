import FrozenTarget_0e8c34f4acbee119
theorem M7.Presentation.presentation_sound : QuantumHarnessFrozenTarget := by
  intro κ σ τ X Y _ _ _ K S T l r m feasible objective mode a ha
  unfold M7.Presentation.present at ha
  rcases ha with ⟨hselected, hleast⟩
  have hspec := ((M7.Presentation.targetLeast_spec κ σ τ X Y K S T l r
    (M7.Presentation.realize l r a)).1 a).mp hleast
  exact ⟨hselected, hspec.1, hspec.2.2⟩
