import FrozenTarget_98dd99959e7753b9
theorem M7.CompactGeneration.emission_signature : QuantumHarnessFrozenTarget := by
  by
    unfold QuantumHarnessFrozenTarget
    intro N inst w E bases
    constructor
    · rfl
    · let c := (M7.CompactGeneration.emission w E bases).leaf
      change M7.RecipeSignature.signature (M7.CanonicalOuter.canonical c) =
        M7.SignatureTau.sourceTau (M7.CanonicalOuter.realizer c).unit
          (M7.RecipeSignature.signature c)
      have h : M7.Action.act (M7.CanonicalOuter.realizer c) c =
          M7.CanonicalOuter.canonical c := by
        exact?
      rw [← h]
      exact M7.RecipeSignature.action_signature N c (M7.CanonicalOuter.realizer c)
