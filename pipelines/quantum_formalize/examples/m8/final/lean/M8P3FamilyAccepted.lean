import M8P3Family

theorem M8.P3Family.divides_modulus : ∀ N : ℕ, 3 ∣ N → M8.P3Family.polynomial ∣ M6.Cyclic.modulus N := by
  change ∀ N : ℕ, 3 ∣ N → M8.P3Family.polynomial ∣ M6.Cyclic.modulus N
  intro N hN
  obtain ⟨k, rfl⟩ := hN
  have h : ∀ k : ℕ, M8.P3Family.polynomial ∣
      (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (3 * k) - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨q * Polynomial.X ^ 3 + (Polynomial.X - 1), ?_⟩
      calc
        Polynomial.X ^ (3 * (k + 1)) - 1 =
            (Polynomial.X ^ (3 * k) - 1) * Polynomial.X ^ 3 +
              (Polynomial.X ^ 3 - 1) := by
                rw [Nat.mul_succ, pow_add]
                ring
        _ = M8.P3Family.polynomial *
            (q * Polynomial.X ^ 3 + (Polynomial.X - 1)) := by
              rw [hq]
              unfold M8.P3Family.polynomial
              ring
  have hone : (-1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    ext n
    by_cases hn : n = 0 <;>
      norm_num [Polynomial.coeff_neg, Polynomial.coeff_one, hn]
  simpa [M6.Cyclic.modulus, sub_eq_add_neg, hone] using h k

theorem M8.P3Family.literal_polynomial : ∀ (N : ℕ) [NeZero N], 3 ≤ N → M7.Supports.polynomial (M8.P3Family.support N) = M8.P3Family.polynomial := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → M7.Supports.polynomial (M8.P3Family.support N) = M8.P3Family.polynomial
  intro N inst hN
  classical
  have h0 : (0 : ZMod N).val = 0 := by simp
  have h1 : (1 : ZMod N).val = 1 := by
    have h : ((1 : ℕ) : ZMod N).val = 1 % N := by
      rw [ZMod.val_natCast]
    simpa only [Nat.cast_one, Nat.mod_eq_of_lt (show 1 < N by omega)] using h
  have h2 : (2 : ZMod N).val = 2 := by
    have h : ((2 : ℕ) : ZMod N).val = 2 % N := by
      rw [ZMod.val_natCast]
    simpa only [Nat.cast_ofNat, Nat.mod_eq_of_lt (show 2 < N by omega)] using h
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have := congrArg ZMod.val h
    omega
  have h02 : (0 : ZMod N) ≠ 2 := by
    intro h
    have := congrArg ZMod.val h
    omega
  have h12 : (1 : ZMod N) ≠ 2 := by
    intro h
    have := congrArg ZMod.val h
    omega
  simp [M8.P3Family.support, M8.P3Family.polynomial, M7.Supports.polynomial,
    h0, h1, h2, h01, h02, h12, add_assoc, add_comm, add_left_comm]

theorem M8.P3Family.nontrivial : M8.P3Family.polynomial ≠ 1 ∧ M8.P3Family.polynomial ≠ 0 ∧ M8.P3Family.polynomial.natDegree = 2 := by
  change M8.P3Family.polynomial ≠ 1 ∧ M8.P3Family.polynomial ≠ 0 ∧ M8.P3Family.polynomial.natDegree = 2
  have hc : M8.P3Family.polynomial.coeff 2 ≠ 0 := by
    norm_num [M8.P3Family.polynomial, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  have hs : (1 + Polynomial.X : M6.Cyclic.BinaryPolynomial).natDegree ≤ 1 := by
    calc
      _ ≤ max (1 : M6.Cyclic.BinaryPolynomial).natDegree (Polynomial.X : M6.Cyclic.BinaryPolynomial).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by simp
  have hd : M8.P3Family.polynomial.natDegree = 2 := by
    apply Nat.le_antisymm
    · unfold M8.P3Family.polynomial
      calc
        _ ≤ max (1 + Polynomial.X : M6.Cyclic.BinaryPolynomial).natDegree (Polynomial.X ^ 2 : M6.Cyclic.BinaryPolynomial).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 2 := max_le (hs.trans (by decide)) (by simp)
    · exact Polynomial.le_natDegree_of_ne_zero hc
  refine ⟨?_, ?_, hd⟩
  · intro h
    simpa [h] using hd
  · intro h
    simpa [h] using hd

theorem M8.P3Family.span_cutoff : ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.Anchor.span (M8.P3Family.recipe N) ≤ M8.Cutoff.limit N := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.Anchor.span (M8.P3Family.recipe N) ≤ M8.Cutoff.limit N
  intro N inst hN
  have hval (k : ℕ) : (k : ZMod N).val ≤ k := by
    rw [ZMod.val_natCast]
    exact Nat.mod_le _ _
  have hs : ∀ i ∈ M8.P3Family.support N, i.val ≤ 2 := by
    intro i hi
    simp only [M8.P3Family.support, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact le_trans (by simpa using hval 0) (by decide : 0 ≤ 2)
    · exact le_trans (by simpa using hval 1) (by decide : 1 ≤ 2)
    · simpa using hval 2
  have hspan : M8.Anchor.span (M8.P3Family.recipe N) ≤ 2 := by
    apply (M8.Anchor.span_le N (M8.P3Family.recipe N) 2).2
    exact ⟨hs, hs⟩
  apply le_trans hspan
  rw [M8.Cutoff.bit_length_limit, Nat.log2_eq_log_two]
  apply le_min
  · omega
  · apply (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega : N + 1 ≠ 0)).2
    norm_num
    omega

theorem M8.P3Family.support_data : ∀ (N : ℕ) [NeZero N], 3 ≤ N → (M8.P3Family.support N).card = 3 ∧ (0 : ZMod N) ∈ M8.P3Family.support N ∧ (1 : ZMod N) ∈ M8.P3Family.support N := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → (M8.P3Family.support N).card = 3 ∧ (0 : ZMod N) ∈ M8.P3Family.support N ∧ (1 : ZMod N) ∈ M8.P3Family.support N
  intro N inst hN
  classical
  have hinj (a b : ℕ) (ha : a < N) (hb : b < N) (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
    have hv := congrArg (fun x : ZMod N => x.val) h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have hh := hinj 0 1 (by omega) (by omega) (by simpa using h)
    omega
  have h02 : (0 : ZMod N) ≠ 2 := by
    intro h
    have hh := hinj 0 2 (by omega) (by omega) (by simpa using h)
    omega
  have h12 : (1 : ZMod N) ≠ 2 := by
    intro h
    have hh := hinj 1 2 (by omega) (by omega) (by simpa using h)
    omega
  simp [M8.P3Family.support, h01, h02, h12]

theorem M8.P3Family.full_direction : ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.CoverageFoundation.FullDirection (M8.P3Family.support N) := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.CoverageFoundation.FullDirection (M8.P3Family.support N)
  intro N inst hN
  apply M8.CoverageFoundation.consecutive_full N (M8.P3Family.support N) 0
  · exact (M8.P3Family.support_data N hN).2.1
  · simpa only [zero_add] using (M8.P3Family.support_data N hN).2.2

theorem M8.P3Family.signature : ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M7.RecipeSignature.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial := by
  intro N inst hN hdiv
  have hl := M8.P3Family.literal_polynomial N hN
  have hd := M8.P3Family.divides_modulus N hdiv
  change EuclideanDomain.gcd
    (EuclideanDomain.gcd (M7.Supports.polynomial (M8.P3Family.support N))
      (M7.Supports.polynomial (M8.P3Family.support N))) (M6.Cyclic.modulus N) = M8.P3Family.polynomial
  rw [hl, EuclideanDomain.gcd_self]
  exact EuclideanDomain.gcd_eq_left.mpr hd

theorem M8.P3Family.valid : ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.PhysicalBridge.Valid 3 (M8.P3Family.recipe N) := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.PhysicalBridge.Valid 3 (M8.P3Family.recipe N)
  intro N inst hN
  classical
  have hs := M8.P3Family.support_data N hN
  have hf := M8.P3Family.full_direction N hN
  have hc : M7.Connectivity.connected (M8.P3Family.support N, M8.P3Family.support N) := by
    simpa only [M7.Connectivity.connected, Set.union_self,
      M8.CoverageFoundation.FullDirection, M8.CoverageFoundation.direction] using hf
  simp_all [M8.PhysicalBridge.Valid, M8.P3Family.recipe]
#print axioms M8.P3Family.divides_modulus
#print axioms M8.P3Family.literal_polynomial
#print axioms M8.P3Family.nontrivial
#print axioms M8.P3Family.signature
#print axioms M8.P3Family.span_cutoff
#print axioms M8.P3Family.support_data
#print axioms M8.P3Family.full_direction
#print axioms M8.P3Family.valid
