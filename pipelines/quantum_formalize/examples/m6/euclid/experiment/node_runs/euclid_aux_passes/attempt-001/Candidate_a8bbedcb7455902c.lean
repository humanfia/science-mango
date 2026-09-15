import FrozenTarget_a8bbedcb7455902c
theorem M6.Euclid.euclid_aux_passes : QuantumHarnessFrozenTarget := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), (M6.Euclid.euclidAux fuel p q).passes = 2 * (M6.Euclid.euclidAux fuel p q).cancellations + 3 * (M6.Euclid.euclidAux fuel p q).rounds + 1
  intro fuel
  induction fuel with
  | zero =>
      intro p q
      rfl
  | succ fuel ih =>
      intro p q
      classical
      simp only [M6.Euclid.euclidAux]
      split <;> simp [M6.Euclid.remainder, ih, M6.Euclid.remainder_passes, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
