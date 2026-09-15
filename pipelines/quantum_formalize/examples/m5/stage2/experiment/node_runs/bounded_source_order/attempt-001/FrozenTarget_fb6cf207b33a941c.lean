import M5Lift

theorem M5.Lift.bounded_progression : ∀ T E L : ℕ, 0 < E → T < L → ∃ j : ℕ, L ≤ T + j * E ∧ T + j * E < L + E := by
  change ∀ T E L : ℕ, 0 < E → T < L → ∃ j : ℕ, L ≤ T + j * E ∧ T + j * E < L + E
  intro T E L hE hTL
  let a := L - T - 1
  have ha : T + a + 1 = L := by
    dsimp [a]
    omega
  have hdiv := Nat.mod_add_div a E
  have hmod := Nat.mod_lt a hE
  rw [Nat.mul_comm E (a / E)] at hdiv
  refine ⟨a / E + 1, ?_⟩
  rw [Nat.add_mul, Nat.one_mul]
  constructor <;> omega
def QuantumHarnessFrozenTarget : Prop :=
  ∀ w T E : ℕ, 2 ≤ w → 0 < T → 0 < E → E ≤ 2 ^ (w * T) → ∃ j : ℕ, M5.packingCutoff w T ≤ T + j * E ∧ T + j * E < M5.birthBound w T
