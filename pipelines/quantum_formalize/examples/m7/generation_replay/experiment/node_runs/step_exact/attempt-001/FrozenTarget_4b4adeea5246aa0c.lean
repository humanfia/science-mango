import M7GenerationReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (e : M7.CompactGeneration.Emission N), M7.GenerationReplay.stepPass w E bases e = true ↔ 0 < M7.CompactGeneration.residual w E bases [] ∧ e = M7.CompactGeneration.emission w E bases
