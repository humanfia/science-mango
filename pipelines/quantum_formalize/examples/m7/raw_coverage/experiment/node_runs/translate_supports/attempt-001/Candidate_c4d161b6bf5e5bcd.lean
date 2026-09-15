import FrozenTarget_c4d161b6bf5e5bcd
theorem M7.RawCoverage.translate_supports : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N hN c s t
  simp [M7.Action.act, M7.Action.translate, M7.Action.affine, M7.Domain.shift, add_comm]
