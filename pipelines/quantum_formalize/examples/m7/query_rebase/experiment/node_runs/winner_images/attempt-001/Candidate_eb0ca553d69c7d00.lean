import FrozenTarget_eb0ca553d69c7d00
theorem M7.QueryRebase.winner_images : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases moves placed
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨M7.QueryRebase.reparam moves x,
      (M7.QueryRebase.winners_reparam H N q bases moves x).mp hx, ?_⟩
    exact (M7.QueryRebase.realize_reparam H N bases moves x).symm.trans hp
  · rintro ⟨x, hx, hp⟩
    have hu := (M7.QueryRebase.reparameterization H N moves).2.1 x
    refine ⟨M7.QueryRebase.undo moves x, ?_, ?_⟩
    · apply (M7.QueryRebase.winners_reparam H N q bases moves
        (M7.QueryRebase.undo moves x)).mpr
      simpa only [hu] using hx
    · rw [M7.QueryRebase.realize_reparam H N bases moves
        (M7.QueryRebase.undo moves x), hu]
      exact hp
