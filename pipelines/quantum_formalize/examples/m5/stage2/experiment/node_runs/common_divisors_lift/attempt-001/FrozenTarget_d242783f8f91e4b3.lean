import M5Lift

theorem M5.Lift.cyclic_as_sub : ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1 := by
  change ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1
  intro N
  simp [M5.cyclicModulus, sub_eq_add_neg, CharTwo.neg_eq]

theorem M5.Lift.modulus_multiple : ∀ E N : ℕ, E ∣ N → M5.cyclicModulus E ∣ M5.cyclicModulus N := by
  change ∀ E N : ℕ, E ∣ N → M5.cyclicModulus E ∣ M5.cyclicModulus N
  intro E N h
  rcases h with ⟨k, rfl⟩
  rw [M5.Lift.cyclic_as_sub, M5.Lift.cyclic_as_sub, pow_mul]
  exact sub_one_dvd_pow_sub_one ((Polynomial.X : M5.BinaryPolynomial) ^ E) k

theorem M5.Lift.progression_difference : ∀ T E j : ℕ, M5.cyclicModulus (T + j * E) - M5.cyclicModulus T = (Polynomial.X : M5.BinaryPolynomial) ^ T * M5.cyclicModulus (j * E) := by
  change ∀ T E j : ℕ, M5.cyclicModulus (T + j * E) - M5.cyclicModulus T = (Polynomial.X : M5.BinaryPolynomial) ^ T * M5.cyclicModulus (j * E)
  intro T E j
  simp only [M5.Lift.cyclic_as_sub, pow_add]
  ring

theorem M5.Lift.progression_congruence : ∀ (G : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → G ∣ M5.cyclicModulus (T + j * E) - M5.cyclicModulus T := by
  change ∀ (G : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → G ∣ M5.cyclicModulus (T + j * E) - M5.cyclicModulus T
  intro G T E j h
  have hE : E ∣ j * E := ⟨j, Nat.mul_comm j E⟩
  have hG := dvd_trans h (M5.Lift.modulus_multiple E (j * E) hE)
  rw [M5.Lift.progression_difference]
  rcases hG with ⟨k, hk⟩
  refine ⟨(Polynomial.X : M5.BinaryPolynomial) ^ T * k, ?_⟩
  rw [hk]
  ring
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (G D : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → D ∣ G → (D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T)
