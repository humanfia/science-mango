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

theorem M5.Lift.cyclic_as_sub : ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1 := by
  change ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1
  intro N
  simp [M5.cyclicModulus, sub_eq_add_neg, CharTwo.neg_eq]

theorem M5.Lift.bounded_source_order : ∀ w T E : ℕ, 2 ≤ w → 0 < T → 0 < E → E ≤ 2 ^ (w * T) → ∃ j : ℕ, M5.packingCutoff w T ≤ T + j * E ∧ T + j * E < M5.birthBound w T := by
  change ∀ w T E : ℕ, 2 ≤ w → 0 < T → 0 < E → E ≤ 2 ^ (w * T) → ∃ j : ℕ, M5.packingCutoff w T ≤ T + j * E ∧ T + j * E < M5.birthBound w T
  intro w T E hw hT hE hbound
  have hcut : T < M5.packingCutoff w T := by
    apply M5.cutoff_gt_period <;> assumption
  obtain ⟨j, hjlo, hjhi⟩ := M5.Lift.bounded_progression T E (M5.packingCutoff w T) hE hcut
  refine ⟨j, hjlo, ?_⟩
  apply M5.source_below_birth_bound <;> omega

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

theorem M5.Lift.common_divisors_lift : ∀ (G D : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → D ∣ G → (D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T) := by
  change ∀ (G D : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → D ∣ G → (D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T)
  intro G D T E j hG hD
  have hd : D ∣ M5.cyclicModulus (T + j * E) - M5.cyclicModulus T :=
    dvd_trans hD (M5.Lift.progression_congruence G T E j hG)
  constructor
  · intro h
    simpa only [sub_sub_cancel] using dvd_sub h hd
  · intro h
    simpa only [sub_add_cancel] using dvd_add hd h

theorem M5.Lift.triple_divisors_lift : ∀ (a b D : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → ((D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus (T + j * E)) ↔ (D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus T)) := by
  change ∀ (a b D : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → ((D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus (T + j * E)) ↔ (D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus T))
  intro a b D T E j hG
  constructor
  · rintro ⟨ha, hb, h⟩
    have hD : D ∣ EuclideanDomain.gcd a b := EuclideanDomain.dvd_gcd ha hb
    exact ⟨ha, hb, (M5.Lift.common_divisors_lift (EuclideanDomain.gcd a b) D T E j hG hD).mp h⟩
  · rintro ⟨ha, hb, h⟩
    have hD : D ∣ EuclideanDomain.gcd a b := EuclideanDomain.dvd_gcd ha hb
    exact ⟨ha, hb, (M5.Lift.common_divisors_lift (EuclideanDomain.gcd a b) D T E j hG hD).mpr h⟩
#print axioms M5.Lift.bounded_progression
#print axioms M5.Lift.bounded_source_order
#print axioms M5.Lift.cyclic_as_sub
#print axioms M5.Lift.modulus_multiple
#print axioms M5.Lift.progression_difference
#print axioms M5.Lift.progression_congruence
#print axioms M5.Lift.common_divisors_lift
#print axioms M5.Lift.triple_divisors_lift
