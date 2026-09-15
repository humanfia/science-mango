import FrozenTarget_d76522b43a3de998
theorem M7.GlobalQuery.winning_fiber : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases x y hclass himage
  classical
  have hf : M7.GlobalQuery.feasible q bases x = M7.GlobalQuery.feasible q bases y := by
    simp only [M7.GlobalQuery.feasible, hclass, himage]
  have ho : M7.GlobalQuery.objective q bases x = M7.GlobalQuery.objective q bases y := by
    simp only [M7.GlobalQuery.objective, himage]
  rw [(M7.GlobalQuery.winners_exact H N q bases).1 x,
    (M7.GlobalQuery.winners_exact H N q bases).1 y, hf, ho]
