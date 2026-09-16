import M8AntipodalFamily

theorem M8.AntipodalFamily.literal_polynomial : ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M7.Supports.polynomial (M8.AntipodalFamily.support N) = M8.AntipodalFamily.polynomial N := by
  classical
  intro N inst hN hEven
  have hhalf : 1 < N / 2 := by omega
  have hlt : N / 2 + 1 < N := by omega
  have hv (k : ℕ) (hk : k < N) : (k : ZMod N).val = k := by
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have v0 : (0 : ZMod N).val = 0 := by simp
  have v1 : (1 : ZMod N).val = 1 := by
    simpa using hv 1 (by omega)
  have vh : ((N / 2 : ℕ) : ZMod N).val = N / 2 := hv _ (by omega)
  have vs : ((N / 2 + 1 : ℕ) : ZMod N).val = N / 2 + 1 := hv _ hlt
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, v1] at hh
    omega
  have h0h : (0 : ZMod N) ≠ ((N / 2 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, vh] at hh
    omega
  have h0s : (0 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, vs] at hh
    omega
  have h1h : (1 : ZMod N) ≠ ((N / 2 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v1, vh] at hh
    omega
  have h1s : (1 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v1, vs] at hh
    omega
  have hhs : ((N / 2 : ℕ) : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [vh, vs] at hh
    omega
  have hn0 : N / 2 ≠ 0 := by omega
  have hn1 : N / 2 ≠ 1 := by omega
  have hs0 : N / 2 + 1 ≠ 0 := by omega
  have hs1 : N / 2 + 1 ≠ 1 := by omega
  simp only [M7.Supports.polynomial, M8.AntipodalFamily.support,
    Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    h01, h0h, h0s, h1h, h1s, hhs, or_self, not_false_eq_true,
    Finset.sum_singleton]
  rw [v0, v1, vh, vs]
  simp only [pow_zero, pow_one, M8.AntipodalFamily.polynomial, pow_succ]
  ring

theorem M8.AntipodalFamily.modulus_power : ∀ (v : ℕ), 3 ≤ v → M6.Cyclic.modulus (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^v) := by
  change ∀ (v : ℕ), 3 ≤ v → M6.Cyclic.modulus (2^v) = (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial)^(2^v)
  intro v hv
  simp [M6.Cyclic.modulus, add_pow_char_pow]

theorem M8.AntipodalFamily.nontrivial : ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → (M8.AntipodalFamily.polynomial N).Monic ∧ M8.AntipodalFamily.polynomial N ≠ 1 ∧ M8.AntipodalFamily.polynomial N ≠ 0 ∧ (M8.AntipodalFamily.polynomial N).natDegree = N/2+1 := by
  intro N inst hN hEven
  have hhalf : 0 < N / 2 := by omega
  have monic_binomial : ∀ (R : Type) [CommRing R] (k : ℕ), 0 < k → (1 + (Polynomial.X : Polynomial R) ^ k).Monic := by
    intro R _ k hk
    first
    | simpa only [Polynomial.C_1, add_comm] using (Polynomial.monic_X_pow_add_C (R := R) (ne_of_gt hk) 1)
    | simpa only [Polynomial.C_1, add_comm] using (Polynomial.monic_X_pow_add_C (R := R) 1 (ne_of_gt hk))
    | simpa only [Polynomial.C_1, add_comm] using (Polynomial.monic_X_pow_add_C (R := R) hk 1)
    | simpa only [Polynomial.C_1, add_comm] using (Polynomial.monic_X_pow_add_C (R := R) 1 hk)
  have h₁ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial)).Monic := by
    simpa using monic_binomial _ 1 (by omega)
  have h₂ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (N / 2)).Monic :=
    monic_binomial _ _ hhalf
  have hm : (M8.AntipodalFamily.polynomial N).Monic := by
    exact h₁.mul h₂
  have hd₁ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial)).natDegree = 1 := by
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simp)]
    simp
  have hd₂ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (N / 2)).natDegree = N / 2 := by
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simpa using hhalf)]
    simp
  have hd : (M8.AntipodalFamily.polynomial N).natDegree = N / 2 + 1 := by
    unfold M8.AntipodalFamily.polynomial
    rw [Polynomial.natDegree_mul h₁.ne_zero h₂.ne_zero, hd₁, hd₂]
    omega
  refine ⟨hm, ?_, hm.ne_zero, hd⟩
  intro heq
  rw [heq, Polynomial.natDegree_one] at hd
  omega

theorem M8.AntipodalFamily.polynomial_power : ∀ (v : ℕ), 3 ≤ v → M8.AntipodalFamily.polynomial (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^(v-1)+1) := by
  intro v hv
  change (1 + Polynomial.X) * (1 + Polynomial.X ^ (2 ^ v / 2)) =
    (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial) ^ (2 ^ (v - 1) + 1)
  have hd : 2 ^ v / 2 = 2 ^ (v - 1) := by
    calc
      2 ^ v / 2 = (2 ^ (v - 1) * 2) / 2 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ v)]
      _ = 2 ^ (v - 1) := by simp
  have hf : (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial) ^ (2 ^ (v - 1)) =
      Polynomial.X ^ (2 ^ (v - 1)) + 1 := by
    simpa using (add_pow_char_pow (Polynomial.X : M6.Cyclic.BinaryPolynomial) 1 2 (v - 1))
  rw [hd, pow_succ, hf]
  ring

theorem M8.AntipodalFamily.divides_modulus : ∀ (v : ℕ), 3 ≤ v → M8.AntipodalFamily.polynomial (2^v) ∣ M6.Cyclic.modulus (2^v) := by
  change ∀ (v : ℕ), 3 ≤ v → M8.AntipodalFamily.polynomial (2^v) ∣ M6.Cyclic.modulus (2^v)
  intro v hv
  rw [M8.AntipodalFamily.polynomial_power v hv, M8.AntipodalFamily.modulus_power v hv]
  have hd : 2 ^ v = 2 ^ (v - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ v)]
  have hp : 0 < (2 : ℕ) ^ (v - 1) := by positivity
  have he : 2 ^ (v - 1) + 1 ≤ 2 ^ v := by omega
  refine ⟨(Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial) ^ (2 ^ v - (2 ^ (v - 1) + 1)), ?_⟩
  rw [← pow_add, Nat.add_sub_of_le he]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → M7.RecipeSignature.signature (M8.AntipodalFamily.recipe N) = M8.AntipodalFamily.polynomial N
