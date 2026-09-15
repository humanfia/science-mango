import FrozenTarget_661e1ff2b5f6d62c
theorem M7.RecipeSignature.sector_meets_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ E : M6.Cyclic.BinaryPolynomial → Prop, ((∃ g : M7.Action.Record N, E (M7.RecipeSignature.signature (M7.Action.act g c))) ↔ ∃ u : (ZMod N)ˣ, E (M7.SignatureTau.sourceTau u (M7.RecipeSignature.signature c)))
  intro N inst c E
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.unit, ?_⟩
    rw [M7.RecipeSignature.action_signature N c g] at hg
    exact hg
  · rintro ⟨u, hu⟩
    refine ⟨{ unit := u, exchange := false, leftShift := 0, rightShift := 0 }, ?_⟩
    rw [M7.RecipeSignature.action_signature N c]
    exact hu
