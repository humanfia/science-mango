import FrozenTarget_e9e6393bb0a89ca0
theorem M5.Lift.bounded_progression : QuantumHarnessFrozenTarget := by
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
