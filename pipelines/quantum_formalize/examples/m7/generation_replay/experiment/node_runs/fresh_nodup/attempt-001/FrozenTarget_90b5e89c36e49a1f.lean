import M7GenerationReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (es : List (M7.CompactGeneration.Emission N)), M7.GenerationReplay.FreshFrom w E bases es → (es.map (fun e => e.representative)).Nodup ∧ ∀ e ∈ es, e.representative ∉ bases
