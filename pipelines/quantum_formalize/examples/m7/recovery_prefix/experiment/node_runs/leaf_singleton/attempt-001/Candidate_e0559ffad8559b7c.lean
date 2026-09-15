import FrozenTarget_e0559ffad8559b7c
theorem M7.RecoveryPrefix.leaf_singleton : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N inst w E p hp x hx
  change x ∈ (M7.PrefixBits.completed N w E p).image (M7.ResiduePrefix.decodePair N) at hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  have hyLeaf := M7.PrefixBits.leaf_singleton N (Nat.pos_of_ne_zero (NeZero.ne N)) w E p hp hy
  have hyEq := Finset.mem_singleton.mp hyLeaf
  subst y
  exact Finset.mem_singleton.mpr rfl
