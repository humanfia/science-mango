import M6Euclid

theorem M6.Euclid.remainder_passes : ∀ (fuel : ℕ) (p q : M6.Euclid.BP), (M6.Euclid.remainderAux fuel p q).passes = 2 * (M6.Euclid.remainderAux fuel p q).cancellations + 1 := by
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

theorem M6.Euclid.euclid_aux_passes : ∀ (fuel : ℕ) (p q : M6.Euclid.BP), (M6.Euclid.euclidAux fuel p q).passes = 2 * (M6.Euclid.euclidAux fuel p q).cancellations + 3 * (M6.Euclid.euclidAux fuel p q).rounds + 1 := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).passes = 2 * (M6.Euclid.euclid p q).cancellations + 3 * (M6.Euclid.euclid p q).rounds + 2
