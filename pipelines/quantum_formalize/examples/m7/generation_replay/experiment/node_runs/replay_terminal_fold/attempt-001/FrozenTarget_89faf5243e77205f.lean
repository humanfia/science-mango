import M7GenerationReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases final : Finset (M7.Action.Recipe N)) (es : List (M7.CompactGeneration.Emission N)), M7.GenerationReplay.replay w E bases es = some final → M7.CompactGeneration.residual w E final [] = 0 ∧ final = es.foldl (fun acc e => insert e.representative acc) bases
