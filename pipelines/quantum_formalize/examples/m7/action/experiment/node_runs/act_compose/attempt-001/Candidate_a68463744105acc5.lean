import FrozenTarget_a68463744105acc5
theorem M7.Action.act_compose : QuantumHarnessFrozenTarget := by
  intro N inst g h c
  rcases g with ⟨u, e, s, t⟩
  rcases h with ⟨v, f, a, b⟩
  cases e <;> cases f <;>
    simp [M7.Action.act, M7.Action.compose, M7.Action.affine,
      Finset.image_image, Function.comp_def, mul_add, mul_assoc, add_assoc]
