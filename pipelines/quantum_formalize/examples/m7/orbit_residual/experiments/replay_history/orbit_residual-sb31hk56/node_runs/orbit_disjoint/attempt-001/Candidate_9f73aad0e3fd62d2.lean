import FrozenTarget_9f73aad0e3fd62d2
theorem M7.OrbitResidual.orbit_disjoint : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c d : M7.Action.Recipe N, Disjoint (M7.ActualOrbit.orbit c) (M7.ActualOrbit.orbit d) ↔ d ∉ M7.ActualOrbit.orbit c
  intro N inst c d
  classical
  constructor
  · intro h hd
    have hself : d ∈ M7.ActualOrbit.orbit d := by
      unfold M7.ActualOrbit.orbit
      exact Finset.mem_image.mpr ⟨M7.Action.identity N, Finset.mem_univ _, M7.Action.act_identity N d⟩
    exact Finset.disjoint_left.mp h hd hself
  · intro hd
    apply Finset.disjoint_left.mpr
    intro y hc hy
    apply hd
    unfold M7.ActualOrbit.orbit at hc hy ⊢
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc hy ⊢
    obtain ⟨g, hg⟩ := hc
    obtain ⟨h, hh⟩ := hy
    refine ⟨M7.Action.compose (M7.Action.inverse h) g, ?_⟩
    rw [M7.Action.act_compose, hg, ← hh, M7.Action.act_inverse]
