import FrozenTarget_087944f9b8339df3
theorem M7.QualityTable.array_scores : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N _ c g
  refine ⟨?_, ?_, ?_⟩
  · simp [M7.QualityTable.leftTable]
  · simp [M7.QualityTable.rightTable]
  · simp [M7.QualityTable.placedScores, M7.QualityTable.read,
      M7.QualityTable.leftTable, M7.QualityTable.rightTable,
      Array.getElem?_eq_getElem, ZMod.val_lt,
      ZMod.natCast_zmod_val]
    <;> rfl
