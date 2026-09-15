import FrozenTarget_9fe522e1eed9d403
theorem M5.Translation.difference_translation : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (c : ZMod N), M5.Translation.differences (M5.Translation.shift S c) = M5.Translation.differences S
  intro N _ S c
  classical
  simp [M5.Translation.differences, M5.Translation.shift, Finset.image_biUnion,
    Finset.image_image, Function.comp_def, add_sub_add_right_eq_sub]
