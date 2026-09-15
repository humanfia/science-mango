import FrozenTarget_e64caf7217879644
theorem M7.CanonicalOuter.canonical_cards : QuantumHarnessFrozenTarget := by
  intro N inst c w h₁ h₂
  simpa only [M7.CanonicalOuter.canonical, M7.CanonicalOuter.candidate,
    M7.CanonicalOuter.normalizePair, M7.CanonicalBlock.normalize_card,
    h₁, h₂, ite_self] using
    (M7.Action.support_cards N
      (M7.CanonicalOuter.outerRecord (M7.CanonicalOuter.chosenOuter c)) c)
