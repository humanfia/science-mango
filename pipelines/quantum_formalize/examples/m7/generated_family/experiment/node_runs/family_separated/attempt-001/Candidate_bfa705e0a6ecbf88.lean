import FrozenTarget_bfa705e0a6ecbf88
theorem M7.GeneratedFamily.family_separated : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  classical
  have hnorm := fun i => (M7.GeneratedFamily.family_good N w E hw hwN hE i).2
  have hsep : ∀ (i j : Fin (M7.GeneratedFamily.size N w E))
      (g h : M7.Action.Record N),
      M7.Action.act g (M7.GeneratedFamily.family N w E i) =
        M7.Action.act h (M7.GeneratedFamily.family N w E j) → i = j := by
    intro i j g h heq
    apply M7.GeneratedFamily.family_injective N w E hw hwN hE
    have hc := congrArg (fun c : M7.Action.Recipe N => M7.CanonicalOuter.canonical c) heq
    simpa only [M7.CanonicalOuter.canonical_invariant, hnorm] using hc
  unfold M7.GlobalQuery.separated
  simp only [M7.GlobalQuery.realize]
  aesop
