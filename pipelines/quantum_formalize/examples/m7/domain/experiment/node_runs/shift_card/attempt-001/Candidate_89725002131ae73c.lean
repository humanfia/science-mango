import FrozenTarget_89725002131ae73c
theorem M7.Domain.shift_card : QuantumHarnessFrozenTarget := by
  intro N inst A r
  classical
  unfold M7.Domain.shift
  apply Finset.card_image_of_injective
  intro a b h
  simpa only [add_left_cancel_iff, add_right_cancel_iff] using h
