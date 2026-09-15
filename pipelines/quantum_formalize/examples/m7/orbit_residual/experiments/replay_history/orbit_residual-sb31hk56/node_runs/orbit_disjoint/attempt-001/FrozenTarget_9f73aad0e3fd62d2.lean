import M7OrbitResidual

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c d : M7.Action.Recipe N, Disjoint (M7.ActualOrbit.orbit c) (M7.ActualOrbit.orbit d) ↔ d ∉ M7.ActualOrbit.orbit c
