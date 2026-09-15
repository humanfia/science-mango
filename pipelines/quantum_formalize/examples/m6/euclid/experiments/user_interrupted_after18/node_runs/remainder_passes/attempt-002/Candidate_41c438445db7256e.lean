import FrozenTarget_41c438445db7256e
theorem M6.Euclid.remainder_passes : QuantumHarnessFrozenTarget := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), (M6.Euclid.remainderAux fuel p q).passes = 2 * (M6.Euclid.remainderAux fuel p q).cancellations + 1
  intro fuel
  induction fuel with
  | zero =>
      intro p q
      rfl
  | succ fuel ih =>
      intro p q
      classical
      simp only [M6.Euclid.remainderAux]
      split <;> simp [ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
