import M8P4Family

theorem M8.P4Family.divides_four : ∀ N : ℕ, 4 ∣ N → M8.P4Family.polynomial ∣ M6.Cyclic.modulus N := by
  change ∀ N : ℕ, 4 ∣ N → M8.P4Family.polynomial ∣ M6.Cyclic.modulus N
  intro N hN
  rcases hN with ⟨k, rfl⟩
  have h : ∀ k : ℕ, M8.P4Family.polynomial ∣ (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (4 * k) - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨q * Polynomial.X ^ 4 + (Polynomial.X - 1), ?_⟩
      rw [Nat.mul_succ, pow_add]
      calc
        Polynomial.X ^ (4 * k) * Polynomial.X ^ 4 - 1 =
            (Polynomial.X ^ (4 * k) - 1) * Polynomial.X ^ 4 + (Polynomial.X ^ 4 - 1) := by ring
        _ = M8.P4Family.polynomial * (q * Polynomial.X ^ 4 + (Polynomial.X - 1)) := by
          rw [hq]
          unfold M8.P4Family.polynomial
          ring
  first
  | simpa only [M6.Cyclic.modulus] using h k
  | have hneg : -(1 : M6.Cyclic.BinaryPolynomial) = 1 := by
      ext n
      by_cases hn : n = 0
      · subst n
        norm_num
      · simp [Polynomial.coeff_one, hn]
    simpa [M6.Cyclic.modulus, sub_eq_add_neg, hneg] using h k

theorem M8.P4Family.literal_polynomial : ∀ (N : ℕ) [NeZero N], 8 ≤ N → M7.Supports.polynomial (M8.P4Family.support N) = M8.P4Family.polynomial := by
  intro N inst hN
  classical
  have hv : ∀ k : ℕ, k < N → (k : ZMod N).val = k := by
    intro k hk
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have h0 : (0 : ZMod N).val = 0 := by simp
  have h1 : (1 : ZMod N).val = 1 := by
    simpa using hv 1 (by omega)
  have h2 : (2 : ZMod N).val = 2 := by
    simpa using hv 2 (by omega)
  have h3 : (3 : ZMod N).val = 3 := by
    simpa using hv 3 (by omega)
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have := congrArg (fun x : ZMod N => x.val) h
    omega
  have h02 : (0 : ZMod N) ≠ 2 := by
    intro h
    have := congrArg (fun x : ZMod N => x.val) h
    omega
  have h03 : (0 : ZMod N) ≠ 3 := by
    intro h
    have := congrArg (fun x : ZMod N => x.val) h
    omega
  have h12 : (1 : ZMod N) ≠ 2 := by
    intro h
    have := congrArg (fun x : ZMod N => x.val) h
    omega
  have h13 : (1 : ZMod N) ≠ 3 := by
    intro h
    have := congrArg (fun x : ZMod N => x.val) h
    omega
  have h23 : (2 : ZMod N) ≠ 3 := by
    intro h
    have := congrArg (fun x : ZMod N => x.val) h
    omega
  simp [M8.P4Family.support, M7.Supports.polynomial, M8.P4Family.polynomial,
    h0, h1, h2, h3, h01, h02, h03, h12, h13, h23,
    add_assoc, add_comm, add_left_comm]

theorem M8.P4Family.nontrivial : M8.P4Family.polynomial ≠ 1 ∧ M8.P4Family.polynomial ≠ 0 ∧ M8.P4Family.polynomial.natDegree = 3 := by
  change M8.P4Family.polynomial ≠ 1 ∧ M8.P4Family.polynomial ≠ 0 ∧ M8.P4Family.polynomial.natDegree = 3
  have h₁ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial)).natDegree = 1 := by
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;> simp
  have h₂ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial) + Polynomial.X ^ 2).natDegree = 2 := by
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;> simp [h₁]
  have h₃ : M8.P4Family.polynomial.natDegree = 3 := by
    unfold M8.P4Family.polynomial
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;> simp [h₂]
  refine ⟨?_, ?_, h₃⟩
  · intro h
    simpa [h] using h₃
  · intro h
    simpa [h] using h₃

theorem M8.P4Family.power_identity : M8.P4Family.polynomial = (Polynomial.X+1)^3 := by
  change (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial (ZMod 2)) = (Polynomial.X + 1) ^ 3
  have h2 : (2 : Polynomial (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3 : Polynomial (ZMod 2)) = 1 := by
    calc
      (3 : Polynomial (ZMod 2)) = 2 + 1 := by ring
      _ = 1 := by rw [h2, zero_add]
  calc
    (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial (ZMod 2)) = Polynomial.X ^ 3 + 3 * Polynomial.X ^ 2 + 3 * Polynomial.X + 1 := by
      rw [h3]
      ring
    _ = (Polynomial.X + 1) ^ 3 := by ring

theorem M8.P4Family.span_cutoff : ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.Anchor.span (M8.P4Family.recipe N) ≤ M8.Cutoff.limit N := by
  intro N inst hN
  classical
  have hv (k : ℕ) : (k : ZMod N).val ≤ k := by
    rw [ZMod.val_natCast]
    exact Nat.mod_le _ _
  have hs : ∀ i ∈ M8.P4Family.support N, i.val ≤ 3 := by
    intro i hi
    simp only [M8.P4Family.support, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · have h : (0 : ZMod N).val ≤ 0 := by simpa using hv 0
      omega
    · have h : (1 : ZMod N).val ≤ 1 := by simpa using hv 1
      omega
    · have h : (2 : ZMod N).val ≤ 2 := by simpa using hv 2
      omega
    · simpa using hv 3
  have hspan : M8.Anchor.span (M8.P4Family.recipe N) ≤ 3 := by
    apply (M8.Anchor.span_le N (M8.P4Family.recipe N) 3).2
    exact ⟨hs, hs⟩
  apply hspan.trans
  change 3 ≤ min (N - 1) (Nat.log 2 (N + 1))
  apply le_min
  · omega
  · apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    norm_num
    omega

theorem M8.P4Family.support_data : ∀ (N : ℕ) [NeZero N], 8 ≤ N → (M8.P4Family.support N).card = 4 ∧ (0 : ZMod N) ∈ M8.P4Family.support N ∧ (1 : ZMod N) ∈ M8.P4Family.support N := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → (M8.P4Family.support N).card = 4 ∧ (0 : ZMod N) ∈ M8.P4Family.support N ∧ (1 : ZMod N) ∈ M8.P4Family.support N
  intro N inst hN
  classical
  have hd (a b : ℕ) (ha : a < N) (hb : b < N) (hab : a ≠ b) : (a : ZMod N) ≠ (b : ZMod N) := by
    intro h
    have hv := congrArg (fun x : ZMod N => x.val) h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    exact hab hv
  have h01 : (0 : ZMod N) ≠ 1 := by
    simpa using hd 0 1 (by omega) (by omega) (by omega)
  have h02 : (0 : ZMod N) ≠ 2 := by
    simpa using hd 0 2 (by omega) (by omega) (by omega)
  have h03 : (0 : ZMod N) ≠ 3 := by
    simpa using hd 0 3 (by omega) (by omega) (by omega)
  have h12 : (1 : ZMod N) ≠ 2 := by
    simpa using hd 1 2 (by omega) (by omega) (by omega)
  have h13 : (1 : ZMod N) ≠ 3 := by
    simpa using hd 1 3 (by omega) (by omega) (by omega)
  have h23 : (2 : ZMod N) ≠ 3 := by
    simpa using hd 2 3 (by omega) (by omega) (by omega)
  simp [M8.P4Family.support, h01, h02, h03, h12, h13, h23]

theorem M8.P4Family.full_direction : ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.CoverageFoundation.FullDirection (M8.P4Family.support N) := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.CoverageFoundation.FullDirection (M8.P4Family.support N)
  intro N inst hN
  apply M8.CoverageFoundation.consecutive_full N (M8.P4Family.support N) 0
  · exact (M8.P4Family.support_data N hN).2.1
  · simpa only [zero_add] using (M8.P4Family.support_data N hN).2.2

theorem M8.P4Family.valid : ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.PhysicalBridge.Valid 4 (M8.P4Family.recipe N) := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.PhysicalBridge.Valid 4 (M8.P4Family.recipe N)
  intro N inst hN
  have hcard := (M8.P4Family.support_data N hN).1
  have hconn : M7.Connectivity.connected (M8.P4Family.recipe N) := by
    simpa [M7.Connectivity.connected, M8.P4Family.recipe,
      M8.CoverageFoundation.FullDirection, M8.CoverageFoundation.direction] using
      (M8.P4Family.full_direction N hN)
  simp_all [M8.PhysicalBridge.Valid, M8.P4Family.recipe]
#print axioms M8.P4Family.divides_four
#print axioms M8.P4Family.literal_polynomial
#print axioms M8.P4Family.nontrivial
#print axioms M8.P4Family.power_identity
#print axioms M8.P4Family.span_cutoff
#print axioms M8.P4Family.support_data
#print axioms M8.P4Family.full_direction
#print axioms M8.P4Family.valid
