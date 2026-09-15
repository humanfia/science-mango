import M7OrbitResidual

theorem M7.OrbitResidual.covered_membership : ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), y ∈ M7.OrbitResidual.covered bases ↔ ∃ c ∈ bases, y ∈ M7.ActualOrbit.orbit c := by
  intro N inst bases y
  classical
  simp only [M7.OrbitResidual.covered, Finset.mem_biUnion]

theorem M7.OrbitResidual.orbit_action : ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (g : M7.Action.Record N), M7.ActualOrbit.orbit (M7.Action.act g c) = M7.ActualOrbit.orbit c := by
  intro N inst c g
  classical
  unfold M7.ActualOrbit.orbit
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨M7.Action.compose h g, ?_⟩
    rw [M7.Action.act_compose]
    exact hh
  · rintro ⟨h, hh⟩
    refine ⟨M7.Action.compose h (M7.Action.inverse g), ?_⟩
    rw [M7.Action.act_compose, M7.Action.act_inverse]
    exact hh

theorem M7.OrbitResidual.orbit_disjoint : ∀ (N : ℕ) [NeZero N], ∀ c d : M7.Action.Recipe N, Disjoint (M7.ActualOrbit.orbit c) (M7.ActualOrbit.orbit d) ↔ d ∉ M7.ActualOrbit.orbit c := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N) (g : M7.Action.Record N), M7.OrbitResidual.Separated bases → y ∉ M7.OrbitResidual.covered bases → M7.OrbitResidual.Separated (insert (M7.Action.act g y) bases)
