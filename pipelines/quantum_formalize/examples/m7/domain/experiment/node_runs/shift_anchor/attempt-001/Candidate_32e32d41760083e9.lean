import FrozenTarget_32e32d41760083e9
theorem M7.Domain.shift_anchor : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N _ A q hq
  classical
  unfold M7.Domain.shift
  apply Finset.mem_image.mpr
  exact ⟨q, hq, by simp⟩
