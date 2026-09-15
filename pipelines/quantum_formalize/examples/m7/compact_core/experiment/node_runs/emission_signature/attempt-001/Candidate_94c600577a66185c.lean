import FrozenTarget_94c600577a66185c
theorem M7.CompactGeneration.emission_signature : QuantumHarnessFrozenTarget := by
  by
    intro N inst w E bases
    constructor
    · rfl
    · change M7.RecipeSignature.signature (M7.CanonicalOuter.canonical (M7.CompactGeneration.emission w E bases).leaf) = M7.SignatureTau.sourceTau (M7.CanonicalOuter.realizer (M7.CompactGeneration.emission w E bases).leaf).unit (M7.RecipeSignature.signature (M7.CompactGeneration.emission w E bases).leaf)
      have h := M7.RecipeSignature.action_signature N (M7.CompactGeneration.emission w E bases).leaf (M7.CanonicalOuter.realizer (M7.CompactGeneration.emission w E bases).leaf)
      first
      | simpa only [M7.CanonicalOuter.realizer_action] using h
      | simpa only [M7.CanonicalOuter.realizer_spec] using h
      | simpa only [M7.CanonicalOuter.realizer_correct] using h
      | simpa only [M7.CanonicalOuter.realizer_act] using h
      | simpa using h
