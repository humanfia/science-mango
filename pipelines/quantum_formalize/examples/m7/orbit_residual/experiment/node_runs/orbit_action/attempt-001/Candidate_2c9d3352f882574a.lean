import FrozenTarget_2c9d3352f882574a
theorem M7.OrbitResidual.orbit_action : QuantumHarnessFrozenTarget := by
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
