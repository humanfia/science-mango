import M7Action

theorem M7.Action.record_card : ∀ (N : ℕ) [NeZero N], Fintype.card (M7.Action.Record N) = Nat.totient N * 2 * N * N := by
  change ∀ (N : ℕ) [NeZero N], Fintype.card (M7.Action.Record N) = Nat.totient N * 2 * N * N
  intro N hN
  let e : M7.Action.Record N ≃ (ZMod N)ˣ × Bool × ZMod N × ZMod N :=
    { toFun := fun g => (g.unit, g.exchange, g.leftShift, g.rightShift)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := by intro g; cases g; rfl
      right_inv := by intro p; rcases p with ⟨u, b, s, t⟩; rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card, Nat.mul_assoc]
def QuantumHarnessFrozenTarget : Prop :=
  Fintype.card (M7.Action.Record 1) = 2
