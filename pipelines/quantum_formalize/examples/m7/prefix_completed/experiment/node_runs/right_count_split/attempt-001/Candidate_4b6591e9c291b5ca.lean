import FrozenTarget_4b6591e9c291b5ca
theorem M7.PrefixCompleted.right_count_split : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro N w E A B WA WB hN hE hBase i hi
  obtain ⟨hLeft, hRight⟩ :=
    M7.PrefixCompleted.right_children N w E A B WA WB i hi hBase
  rw [M7.PrefixCompleted.count_completed N w E A B WA WB hN hE hBase,
    M7.PrefixCompleted.count_completed N w E A B WA (WB.erase i) hN hE hLeft,
    M7.PrefixCompleted.count_completed N w E A (insert i B) WA (WB.erase i) hN hE hRight]
  rcases hBase with ⟨hA0, hB0, hA, hB, hWA, hWB, hDA, hDB⟩
  rw [M7.PrefixCompleted.right_sets N w E A B WA WB hDA hDB i hi,
    Finset.card_union_of_disjoint
      (M7.PrefixCompleted.right_disjoint N w E A B WA WB hDA hDB i hi)]
  simp only [Nat.cast_add]
