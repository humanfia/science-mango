import FrozenTarget_4f4a577d6c85cbfa
theorem M6.Euclid.remainder_passes : QuantumHarnessFrozenTarget := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), (M6.Euclid.remainderAux fuel p q).passes = 2 * (M6.Euclid.remainderAux fuel p q).cancellations + 1
  intro fuel
  induction fuel with
  | zero =>
      intro p q
      simp [M6.Euclid.remainderAux]
  | succ fuel ih =>
      intro p q
      simp only [M6.Euclid.remainderAux]
      repeat' first | split | progress dsimp only
      all_goals simp_all [ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
