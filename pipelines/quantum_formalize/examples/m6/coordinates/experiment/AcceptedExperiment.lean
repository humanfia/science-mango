import M6Coordinates

theorem M6.Coordinates.block_coeff : ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N) (i : Fin N), (M6.Coordinates.blockPolynomial N h).coeff i.val = h (i.val : ZMod N) := by
  intro N inst h i
  classical
  simp [M6.Coordinates.blockPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Fin.val_eq_val, i.isLt]

theorem M6.Coordinates.block_degree : ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N), (M6.Coordinates.blockPolynomial N h).degree < (N : WithBot ℕ) := by
  intro N _ h
  classical
  unfold M6.Coordinates.blockPolynomial
  simp only [Polynomial.C_mul_X_pow_eq_monomial]
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  apply (Finset.sup_lt_iff (by simp)).2
  intro i hi
  apply lt_of_le_of_lt (Polynomial.degree_monomial_le _ _)
  first
  | exact_mod_cast i.isLt
  | exact_mod_cast ZMod.val_lt i
  | exact_mod_cast Finset.mem_range.mp hi

theorem M6.Coordinates.block_reconstruct : ∀ (N : ℕ) [NeZero N] (p : M6.Cyclic.BinaryPolynomial), p.degree < (N : WithBot ℕ) → M6.Coordinates.blockPolynomial N (M6.Coordinates.coefficients N p) = p := by
  intro N inst p hp
  classical
  change (∑ i : Fin N, Polynomial.C (p.coeff ((i.val : ZMod N).val)) * Polynomial.X ^ i.val) = p
  have hval (i : Fin N) : (i.val : ZMod N).val = i.val := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  simp only [hval]
  ext k
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k < N
  · rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin N)]
    · simp
    · intro i hi hne
      have hv : i.val ≠ k := by
        intro h
        apply hne
        exact Fin.ext h
      simp [Polynomial.coeff_C_mul_X_pow, hv, Ne.symm hv]
    · simp
  · have hNk : N ≤ k := Nat.le_of_not_gt hk
    have hdeg : p.degree < (k : WithBot ℕ) := by
      apply lt_of_lt_of_le hp
      exact_mod_cast hNk
    rw [Polynomial.coeff_eq_zero_of_degree_lt hdeg]
    apply Finset.sum_eq_zero
    intro i hi
    have hv : i.val ≠ k := by
      intro h
      exact hk (h ▸ i.isLt)
    simp [Polynomial.coeff_C_mul_X_pow, hv, Ne.symm hv]

theorem M6.Coordinates.encode_sum : ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N), M6.Coordinates.encode N h = ∑ i : ZMod N, AdjoinRoot.of (M6.Cyclic.modulus N) (h i) * M6.Coordinates.rootPow N i := by
  intro N inst h
  classical
  let e : Fin N ≃ ZMod N :=
    { toFun := fun i => (i.val : ZMod N)
      invFun := fun i => ⟨i.val, ZMod.val_lt i⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact (ZMod.val_natCast N i.val).trans (Nat.mod_eq_of_lt i.isLt)
      right_inv := fun i => ZMod.natCast_zmod_val i }
  have hv (i : Fin N) : (i.val : ZMod N).val = i.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  have hs := e.sum_comp (fun i : ZMod N =>
    AdjoinRoot.of (M6.Cyclic.modulus N) (h i) *
      AdjoinRoot.root (M6.Cyclic.modulus N) ^ i.val)
  change (∑ i : Fin N,
    AdjoinRoot.of (M6.Cyclic.modulus N) (h (i.val : ZMod N)) *
      AdjoinRoot.root (M6.Cyclic.modulus N) ^ (i.val : ZMod N).val) = _ at hs
  simp only [hv] at hs
  simpa only [M6.Coordinates.encode, M6.Coordinates.blockPolynomial,
    M6.Cyclic.image, M6.Coordinates.rootPow, map_sum, map_mul, map_pow,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X] using hs

theorem M6.Coordinates.modulus_monic_degree : ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic ∧ (M6.Cyclic.modulus N).natDegree = N := by
  change ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic ∧ (M6.Cyclic.modulus N).natDegree = N
  intro N inst
  change (Polynomial.X ^ N + (1 : Polynomial (ZMod 2))).Monic ∧ (Polynomial.X ^ N + (1 : Polynomial (ZMod 2))).natDegree = N
  constructor
  · simpa only [Polynomial.C_1] using (Polynomial.monic_X_pow_add_C (1 : ZMod 2) (NeZero.ne N))
  · simpa only [Polynomial.C_1] using (Polynomial.natDegree_X_pow_add_C (n := N) (r := (1 : ZMod 2)))

theorem M6.Coordinates.root_period : ∀ (N : ℕ) [NeZero N], (AdjoinRoot.root (M6.Cyclic.modulus N))^N = 1 := by
  change ∀ (N : ℕ) [NeZero N], (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ N = 1
  intro N hN
  have h := AdjoinRoot.eval₂_root (M6.Cyclic.modulus N)
  change Polynomial.eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) (AdjoinRoot.root (M6.Cyclic.modulus N)) (Polynomial.X ^ N + 1) = 0 at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one] at h
  have h₂ : (1 : ZMod 2) + 1 = 0 := by decide
  have h₂' : (1 : AdjoinRoot (M6.Cyclic.modulus N)) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (AdjoinRoot.of (M6.Cyclic.modulus N)) h₂
  exact add_right_cancel (h.trans h₂'.symm)

theorem M6.Coordinates.encode_injective : ∀ (N : ℕ) [NeZero N], Function.Injective (M6.Coordinates.encode N) := by
  change ∀ (N : ℕ) [NeZero N], Function.Injective (M6.Coordinates.encode N)
  intro N inst h k heq
  classical
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N h) = AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N k) at heq
  have hdiv := AdjoinRoot.mk_eq_mk.mp heq
  obtain ⟨hm, hnat⟩ := M6.Coordinates.modulus_monic_degree N
  have hmdeg : (M6.Cyclic.modulus N).degree = (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hnat]
  have hlt : (M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k).degree < (M6.Cyclic.modulus N).degree := by
    rw [hmdeg]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (M6.Coordinates.block_degree N h) (M6.Coordinates.block_degree N k))
  have hz : M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k = 0 := by
    by_contra hn
    have hle : (M6.Cyclic.modulus N).degree ≤ (M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k).degree := by
      first
      | exact Polynomial.degree_le_of_dvd hdiv hn
      | exact Polynomial.degree_le_of_dvd hn hdiv
    exact (not_lt_of_ge hle) hlt
  have hp := sub_eq_zero.mp hz
  funext i
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff i.val) hp
  rw [M6.Coordinates.block_coeff N h ⟨i.val, ZMod.val_lt i⟩, M6.Coordinates.block_coeff N k ⟨i.val, ZMod.val_lt i⟩] at hc
  simpa using hc

theorem M6.Coordinates.encode_polynomial : ∀ (N : ℕ) [NeZero N] (p : M6.Cyclic.BinaryPolynomial), p.degree < (N : WithBot ℕ) → M6.Coordinates.encode N (M6.Coordinates.coefficients N p) = M6.Cyclic.image N p := by
  intro N inst p hp
  change M6.Cyclic.image N (M6.Coordinates.blockPolynomial N (M6.Coordinates.coefficients N p)) = M6.Cyclic.image N p
  rw [M6.Coordinates.block_reconstruct N p hp]

theorem M6.Coordinates.encode_surjective : ∀ (N : ℕ) [NeZero N], Function.Surjective (M6.Coordinates.encode N) := by
  change ∀ (N : ℕ) [NeZero N], Function.Surjective (M6.Coordinates.encode N)
  intro N inst y
  classical
  refine AdjoinRoot.induction_on _ y ?_
  intro p
  obtain ⟨hm, hn⟩ := M6.Coordinates.modulus_monic_degree N
  have hd : (M6.Cyclic.modulus N).degree = (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hn]
  have hr : (p %ₘ M6.Cyclic.modulus N).degree < (N : WithBot ℕ) := by
    rw [← hd]
    exact Polynomial.degree_modByMonic_lt p hm
  refine ⟨M6.Coordinates.coefficients N (p %ₘ M6.Cyclic.modulus N), ?_⟩
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N (M6.Coordinates.coefficients N (p %ₘ M6.Cyclic.modulus N))) = AdjoinRoot.mk (M6.Cyclic.modulus N) p
  rw [M6.Coordinates.block_reconstruct N _ hr]
  symm
  apply AdjoinRoot.mk_eq_mk.mpr
  rw [Polynomial.modByMonic_eq_sub_mul_div, sub_sub_cancel]
  exact dvd_mul_right _ _

theorem M6.Coordinates.rootPow_add : ∀ (N : ℕ) [NeZero N] (i j : ZMod N), M6.Coordinates.rootPow N (i+j) = M6.Coordinates.rootPow N i * M6.Coordinates.rootPow N j := by
  change ∀ (N : ℕ) [NeZero N] (i j : ZMod N), M6.Coordinates.rootPow N (i + j) = M6.Coordinates.rootPow N i * M6.Coordinates.rootPow N j
  intro N hN i j
  change (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ (i + j).val = (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ i.val * (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ j.val
  rw [ZMod.val_add, ← pow_add]
  have h := congrArg (fun k : ℕ => (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ k) (Nat.mod_add_div (i.val + j.val) N)
  simpa only [pow_add, pow_mul, M6.Coordinates.root_period, one_pow, mul_one] using h

theorem M6.Coordinates.encode_conv : ∀ (N : ℕ) [NeZero N] (a h : M6.Physical.Block N), M6.Coordinates.encode N (M6.Physical.conv N a h) = M6.Coordinates.encode N a * M6.Coordinates.encode N h := by
  change ∀ (N : ℕ) [NeZero N] (a h : M6.Physical.Block N), M6.Coordinates.encode N (M6.Physical.conv N a h) = M6.Coordinates.encode N a * M6.Coordinates.encode N h
  intro N inst a h
  classical
  let f := AdjoinRoot.of (M6.Cyclic.modulus N)
  let p := M6.Coordinates.rootPow N
  calc
    M6.Coordinates.encode N (M6.Physical.conv N a h) =
        ∑ r : ZMod N, ∑ t : ZMod N, f (a r) * f (h (t - r)) * p t := by
      rw [M6.Coordinates.encode_sum]
      simp only [M6.Physical.conv, map_sum, map_mul, Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ r : ZMod N, ∑ s : ZMod N,
        (f (a r) * p r) * (f (h s) * p s) := by
      apply Finset.sum_congr rfl
      intro r hr
      let e : ZMod N ≃ ZMod N :=
        { toFun := fun s => r + s
          invFun := fun t => t - r
          left_inv := by intro s; dsimp; abel
          right_inv := by intro t; dsimp; abel }
      have hs := e.sum_comp (fun t => f (a r) * f (h (t - r)) * p t)
      rw [← hs]
      apply Finset.sum_congr rfl
      intro s hs
      change f (a r) * f (h (r + s - r)) * M6.Coordinates.rootPow N (r + s) = _
      rw [add_sub_cancel_left, M6.Coordinates.rootPow_add]
      change f (a r) * f (h s) * (p r * p s) = (f (a r) * p r) * (f (h s) * p s)
      ring
    _ = M6.Coordinates.encode N a * M6.Coordinates.encode N h := by
      rw [M6.Coordinates.encode_sum, M6.Coordinates.encode_sum]
      change (∑ r : ZMod N, ∑ s : ZMod N, (f (a r) * p r) * (f (h s) * p s)) =
        (∑ r : ZMod N, f (a r) * p r) * (∑ s : ZMod N, f (h s) * p s)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
#print axioms M6.Coordinates.block_coeff
#print axioms M6.Coordinates.block_degree
#print axioms M6.Coordinates.block_reconstruct
#print axioms M6.Coordinates.encode_polynomial
#print axioms M6.Coordinates.encode_sum
#print axioms M6.Coordinates.modulus_monic_degree
#print axioms M6.Coordinates.encode_injective
#print axioms M6.Coordinates.encode_surjective
#print axioms M6.Coordinates.root_period
#print axioms M6.Coordinates.rootPow_add
#print axioms M6.Coordinates.encode_conv
