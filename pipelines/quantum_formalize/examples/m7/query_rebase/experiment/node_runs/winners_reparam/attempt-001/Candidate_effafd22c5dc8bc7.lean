import FrozenTarget_effafd22c5dc8bc7
theorem M7.QueryRebase.winners_reparam : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases moves x
  rw [(M7.GlobalQuery.winners_exact H N q (M7.QueryRebase.rebase bases moves)).1 x,
    (M7.GlobalQuery.winners_exact H N q bases).1 (M7.QueryRebase.reparam moves x)]
  have hx := M7.QueryRebase.feasible_objective H N q bases moves x
  constructor
  · rintro ⟨hfx, hopt⟩
    refine ⟨hx.1.mp hfx, ?_⟩
    intro y hfy
    obtain ⟨z, rfl⟩ := (M7.QueryRebase.reparameterization H N moves).2.2.2 y
    have hz := M7.QueryRebase.feasible_objective H N q bases moves z
    have h := hopt z (hz.1.mpr hfy)
    simpa only [hz.2, hx.2] using h
  · rintro ⟨hfx, hopt⟩
    refine ⟨hx.1.mpr hfx, ?_⟩
    intro y hfy
    have hy := M7.QueryRebase.feasible_objective H N q bases moves y
    rw [hy.2, hx.2]
    exact hopt (M7.QueryRebase.reparam moves y) (hy.1.mp hfy)
