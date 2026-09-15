import FrozenTarget_cbb73368452545ce
theorem M7.CanonicalOuter.realizer_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.CanonicalOuter.realizer c) c = M7.CanonicalOuter.canonical c
  intro N _ c
  classical
  have hs (s : ZMod N) (A : M7.CanonicalBlock.Support N) :
      A.image (M7.Action.affine 1 s) = M7.CanonicalBlock.shift s A := by
    unfold M7.Action.affine M7.CanonicalBlock.shift
    simp [add_comm]
  have hn (r : M7.Action.Recipe N) :
      M7.Action.act
        (M7.Action.translate (-M7.CanonicalBlock.bestAnchor r.1)
          (-M7.CanonicalBlock.bestAnchor r.2)) r =
        M7.CanonicalOuter.normalizePair r := by
    change
      (r.1.image (M7.Action.affine 1 (-M7.CanonicalBlock.bestAnchor r.1)),
        r.2.image (M7.Action.affine 1 (-M7.CanonicalBlock.bestAnchor r.2))) =
      (M7.CanonicalBlock.shift (-M7.CanonicalBlock.bestAnchor r.1) r.1,
        M7.CanonicalBlock.shift (-M7.CanonicalBlock.bestAnchor r.2) r.2)
    exact Prod.ext (hs _ _) (hs _ _)
  unfold M7.CanonicalOuter.realizer
  rw [M7.Action.act_compose]
  exact hn _
