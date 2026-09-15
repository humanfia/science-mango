import M7RecipeSignatureReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ (M6.Cyclic.modulus N) → (M7.SignatureTau.tau u F).natDegree = F.natDegree
