import M7FinalResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∀ (x : M7.GlobalQuery.Index H N) (j : Fin q.objectives.length), 1 + (M7.GlobalQuery.objective q bases x j).natAbs.size ≤ M7.FinalResources.objectiveBits q bases
