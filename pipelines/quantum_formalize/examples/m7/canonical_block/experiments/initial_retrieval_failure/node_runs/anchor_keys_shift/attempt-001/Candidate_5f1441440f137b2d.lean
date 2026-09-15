import FrozenTarget_5f1441440f137b2d
theorem M7.CanonicalBlock.anchor_keys_shift : QuantumHarnessFrozenTarget := by
  intro N inst s A
  classical
  unfold M7.CanonicalBlock.candidates
  simp only [Finset.image_image, Function.comp_def]
  change (M7.CanonicalBlock.shift s A).image (fun q => M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) (M7.CanonicalBlock.shift s A))) = A.image (fun q => M7.CanonicalBlock.key (M7.CanonicalBlock.shift (-q) A))
  simp only [M7.CanonicalBlock.shift, Finset.image_image, Function.comp_def]
  apply Finset.image_congr rfl
  intro q hq
  apply congrArg M7.CanonicalBlock.key
  apply Finset.image_congr rfl
  intro i hi
   dsimp only
   abel
