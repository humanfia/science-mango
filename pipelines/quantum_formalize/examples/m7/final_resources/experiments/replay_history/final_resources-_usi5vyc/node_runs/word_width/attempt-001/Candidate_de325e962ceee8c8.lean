import FrozenTarget_de325e962ceee8c8
theorem M7.FinalResources.word_width : QuantumHarnessFrozenTarget := by
  classical
  intro H N inst q bases x j
  unfold M7.FinalResources.objectiveBits
  apply Nat.add_le_add_left
  exact le_trans
    (Finset.le_sup (f := fun k : Fin q.objectives.length =>
      (M7.GlobalQuery.objective q bases x k).natAbs.size) (Finset.mem_univ j))
    (Finset.le_sup (f := fun y : M7.GlobalQuery.Index H N =>
      Finset.univ.sup (fun k : Fin q.objectives.length =>
        (M7.GlobalQuery.objective q bases y k).natAbs.size)) (Finset.mem_univ x))
