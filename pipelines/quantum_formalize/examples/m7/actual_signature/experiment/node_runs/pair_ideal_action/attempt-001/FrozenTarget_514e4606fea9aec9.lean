import M7RecipeSignatureReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.SignatureIdeal.pairIdeal N (M7.Supports.polynomial (M7.Action.act g c).1) (M7.Supports.polynomial (M7.Action.act g c).2) = (M7.SignatureIdeal.pairIdeal N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)).map (M7.QuotientAuto.substitution g.unit)
