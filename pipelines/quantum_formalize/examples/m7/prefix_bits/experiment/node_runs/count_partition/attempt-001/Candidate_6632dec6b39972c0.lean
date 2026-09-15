import FrozenTarget_6632dec6b39972c0
theorem M7.PrefixBits.count_partition : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N hN w E p hE hp
  classical
  rcases M7.PrefixBits.completed_partition N hN w E p hp with ⟨hu, hd⟩
  rw [M7.PrefixBits.count_card N hN w E p hE,
    M7.PrefixBits.count_card N hN w E (p ++ [false]) hE,
    M7.PrefixBits.count_card N hN w E (p ++ [true]) hE,
    hu, Finset.card_union_of_disjoint hd, Nat.cast_add]
