import FrozenTarget_b211fd49aee2a46c
theorem M8.Diagonal.logical_lower_bound : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (p : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), p ≠ 0 → v ∈ M6.Spaces.logicalWords N p p → 2 ≤ M6.Pinned.weight v
  intro N inst p v hp hv
  by_contra h
  have hw : M6.Pinned.weight v < 2 := by omega
  have hs := ((M6.Spaces.logical_words_iff N p p v).mp hv).1
  have hw' : M6.Physical.wordWeight N (M6.Flatten.unflatten N v) < 2 := by
    rw [← M6.Flatten.flatten_weight N, M6.Flatten.flatten_right N]
    exact hw
  have hz := M8.Diagonal.small_cycle_zero N p (M6.Flatten.unflatten N v) hp hs hw'
  have hf0 : M6.Flatten.flatten N (0 : M6.Physical.Word N) = 0 := by
    simpa only [zero_smul] using (M6.Flatten.flatten_smul N (0 : ZMod 2) (0 : M6.Physical.Word N))
  have hv0 : v = 0 := by
    calc
      v = M6.Flatten.flatten N (M6.Flatten.unflatten N v) := (M6.Flatten.flatten_right N v).symm
      _ = M6.Flatten.flatten N 0 := congrArg (M6.Flatten.flatten N) hz
      _ = 0 := hf0
  apply M6.Spaces.zero_not_logical N p p
  simpa only [hv0] using hv
