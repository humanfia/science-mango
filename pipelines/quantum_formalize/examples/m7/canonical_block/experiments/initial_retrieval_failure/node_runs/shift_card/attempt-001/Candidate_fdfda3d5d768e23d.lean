import FrozenTarget_fdfda3d5d768e23d
theorem M7.CanonicalBlock.shift_card : QuantumHarnessFrozenTarget := by
  intro N inst s A
  classical
  change (A.image (fun i => i + s)).card = A.card
  apply Finset.card_image_of_injective
  intro a b h
  exact add_right_cancel h
