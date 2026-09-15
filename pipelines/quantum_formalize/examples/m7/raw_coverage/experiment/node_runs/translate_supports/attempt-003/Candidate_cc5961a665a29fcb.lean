import FrozenTarget_cc5961a665a29fcb
theorem M7.RawCoverage.translate_supports : QuantumHarnessFrozenTarget := by
  intro N hN c s t
  apply Prod.ext <;> ext x
  all_goals
    simp [M7.Action.act, M7.Action.translate, M7.Action.affine, M7.Domain.shift, Finset.mem_image]
  all_goals
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [add_assoc] using ha
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp [add_assoc]
