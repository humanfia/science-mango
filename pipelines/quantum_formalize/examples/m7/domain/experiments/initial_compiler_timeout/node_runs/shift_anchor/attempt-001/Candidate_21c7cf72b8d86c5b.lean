import FrozenTarget_21c7cf72b8d86c5b
theorem M7.Domain.shift_anchor : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N _ A q hq
  classical
  unfold M7.Domain.shift
  apply Finset.mem_image.mpr
  exact ⟨q, hq, by simp⟩
