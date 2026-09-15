import FrozenTarget_2b7f2e9cc26e3f29
theorem M7.QualityTable.array_scores : QuantumHarnessFrozenTarget := by
  intro N inst c g
  refine ⟨?_, ?_, ?_⟩
  · simp [M7.QualityTable.leftTable]
  · simp [M7.QualityTable.rightTable]
  · simp [M7.QualityTable.placedScores, M7.QualityTable.read,
      M7.QualityTable.leftTable, M7.QualityTable.rightTable,
      ZMod.val_lt, ZMod.natCast_zmod_val]
    constructor <;> rfl
