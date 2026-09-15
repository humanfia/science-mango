import FrozenTarget_1fa1a58c2745cd29
theorem M7.CompactStorage.emission_valid : QuantumHarnessFrozenTarget := by
  intro N inst w E bases
  unfold M7.CompactStorage.Valid
  repeat' apply And.intro
  all_goals first
    | exact (M7.CompactGeneration.emission_action N w E bases).1
    | exact (M7.CompactGeneration.emission_stabilizer N w E bases).2
    | rfl
