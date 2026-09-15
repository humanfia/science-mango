import FrozenTarget_531608b022a6b72b
theorem M7.CanonicalClasses.normalized_separated : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ bases : Finset (M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → M7.OrbitResidual.Separated bases
  intro N _ bases hnorm
  classical
  unfold M7.OrbitResidual.Separated
  intro c hc d hd hcd
  apply Finset.disjoint_left.mpr
  intro y hyc hyd
  apply hcd
  calc
    c = M7.CanonicalOuter.canonical c := (hnorm c hc).symm
    _ = M7.CanonicalOuter.canonical y := ((M7.CanonicalClasses.orbit_membership N c y).mp hyc).symm
    _ = M7.CanonicalOuter.canonical d := (M7.CanonicalClasses.orbit_membership N d y).mp hyd
    _ = d := hnorm d hd
