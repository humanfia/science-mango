import M7LabelReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (r : M7.LabelReplay.Certificate N), M7.LabelReplay.check c r = true → r.signature = M7.RecipeSignature.signature c ∧ (∀ i : Fin (2*N+1), r.coefficients i = (M7.LabelReplay.Q c (M6.Pinned.free (2*N))).coeff i.val) ∧ r.answer = M6.ActualTransfer.solve N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ∧ r.pins = M7.LabelReplay.pinData c
