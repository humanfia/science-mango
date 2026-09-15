import FrozenTarget_417486606361a81f
theorem M7.StreamingIndices.record_surjective : QuantumHarnessFrozenTarget := by
  classical
  intro N inst g
  rcases g with ⟨v, b, s, t⟩
  cases b
  · refine ⟨Fintype.equivFin ((ZMod N)ˣ) v, 0, ⟨s.val, ZMod.val_lt s⟩, ⟨t.val, ZMod.val_lt t⟩, ?_⟩
    simp [M7.StreamingIndices.decodeRecord, ZMod.natCast_zmod_val]
  · refine ⟨Fintype.equivFin ((ZMod N)ˣ) v, 1, ⟨s.val, ZMod.val_lt s⟩, ⟨t.val, ZMod.val_lt t⟩, ?_⟩
    simp [M7.StreamingIndices.decodeRecord, ZMod.natCast_zmod_val]
