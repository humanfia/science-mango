import FrozenTarget_b99cebc988066bb4
theorem M6.Transfer.uniform_matrix_power : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro S K _ _ _ A N
  induction N with
  | zero => rfl
  | succ n ih =>
      simpa only [M6.Transfer.matrixProduct, pow_succ] using congrArg (fun B : Matrix S S K => B * A) ih
