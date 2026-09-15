import FrozenTarget_7a63194371298ef8
theorem M6.Transfer.shift_coordinates : QuantumHarnessFrozenTarget := by
  intro R m t
  constructor
  · rfl
  · intro j
    unfold M6.Transfer.shift
    split
    · rename_i h
      change j.val + 1 = 0 at h
      omega
    · apply congrArg m
      apply Fin.ext
      simp
