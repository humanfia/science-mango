import FrozenTarget_558038642ca5170c
theorem M7.CompactGeneration.emission_signature : QuantumHarnessFrozenTarget := by
  intro N inst w E bases
  constructor
  · rfl
  · let c := (M7.CompactGeneration.emission w E bases).leaf
    change M7.RecipeSignature.signature (M7.CanonicalOuter.canonical c) =
      M7.SignatureTau.sourceTau (M7.CanonicalOuter.realizer c).unit
        (M7.RecipeSignature.signature c)
    have h : M7.Action.act (M7.CanonicalOuter.realizer c) c =
        M7.CanonicalOuter.canonical c := by
      first
      | exact M7.CanonicalOuter.realizer_spec N c
      | exact M7.CanonicalOuter.realizer_spec c
      | exact M7.CanonicalOuter.realizer_correct N c
      | exact M7.CanonicalOuter.realizer_correct c
      | exact M7.CanonicalOuter.realizer_action N c
      | exact M7.CanonicalOuter.realizer_action c
      | exact M7.CanonicalOuter.realizes N c
      | exact M7.CanonicalOuter.realizes c
      | unfold M7.CanonicalOuter.realizer
        exact Classical.choose_spec _
    rw [← h]
    exact M7.RecipeSignature.action_signature N c (M7.CanonicalOuter.realizer c)
