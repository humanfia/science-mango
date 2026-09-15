import FrozenTarget_373641ff534262f1
theorem M6.EuclidStorage.rem_loop_refines : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t
      simp [M6.EuclidStorage.remLoop, M6.Euclid.remainderAux]
  | succ fuel ih =>
      intro s c t
      simp only [M6.EuclidStorage.remLoop, M6.Euclid.remainderAux]
      split <;> simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
