import M7RecipeSignatureReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.RecipeSignature.signature c).Monic ∧ M7.RecipeSignature.signature c ∣ (M6.Cyclic.modulus N)
