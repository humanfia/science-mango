import FrozenTarget_1e5d8f209e1e571a
theorem M6.Character.free_character_factor : QuantumHarnessFrozenTarget := by
  intro m i s
  classical
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  simp [M6.Character.pinnedCharacterFactor, h,
    M6.Character.boundaryFactor, M6.Pinned.free, M6.Character.sign]
