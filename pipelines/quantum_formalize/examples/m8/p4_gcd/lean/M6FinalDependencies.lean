import M6FinalClaims

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

theorem M6.BoundaryFibers.annihilator_general : ∀ (F M : M6.BoundaryFibers.BP), F.Monic → F ∣ M → M ≠ 0 → Nat.card {h : AdjoinRoot M // AdjoinRoot.mk M F * h = 0} = 2^F.natDegree := by
  intro F M hF hFM hM
  rcases hFM with ⟨K, rfl⟩
  have hK : K ≠ 0 := by
    intro hK
    apply hM
    simp [hK]
  simpa only [M6.KernelFibers.annihilator] using
    (M6.KernelFibers.annihilator_card F K hF hK)

theorem M6.BoundaryFibers.boundary_add : ∀ (a b M : M6.BoundaryFibers.BP) (h k : AdjoinRoot M), M6.BoundaryFibers.boundary a b M (h+k) = M6.BoundaryFibers.boundary a b M h + M6.BoundaryFibers.boundary a b M k := by
  intro a b M h k
  unfold M6.BoundaryFibers.boundary
  apply Prod.ext <;> exact mul_add _ _ _

theorem M6.BoundaryFibers.kernel_iff : ∀ (a b M : M6.BoundaryFibers.BP) (h : AdjoinRoot M), M6.BoundaryFibers.boundary a b M h = (0,0) ↔ AdjoinRoot.mk M (M6.Cyclic.signature a b M) * h = 0 := by
  change ∀ (a b M : M6.BoundaryFibers.BP) (h : AdjoinRoot M), M6.BoundaryFibers.boundary a b M h = (0, 0) ↔ AdjoinRoot.mk M (M6.Cyclic.signature a b M) * h = 0
  intro a b M h
  refine AdjoinRoot.induction_on M h ?_
  intro p
  simpa only [M6.BoundaryFibers.boundary, Prod.mk.injEq, ← map_mul, AdjoinRoot.mk_eq_zero, and_comm] using M6.Cyclic.kernel_divisibility a b M p

theorem M6.BoundaryFibers.nonzero_monic : ∀ p : M6.BoundaryFibers.BP, p ≠ 0 → p.Monic := by
  change ∀ p : M6.BoundaryFibers.BP, p ≠ 0 → p.Monic
  intro p hp
  have hlc : p.leadingCoeff ≠ 0 := by
    intro h
    exact hp (Polynomial.leadingCoeff_eq_zero.mp h)
  change p.leadingCoeff = 1
  have hbinary : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact hbinary p.leadingCoeff hlc

theorem M6.BoundaryFibers.signature_nonzero : ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → M6.Cyclic.signature a b M ≠ 0 := by
  change ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → M6.Cyclic.signature a b M ≠ 0
  intro a b M hM hs
  have hd := (M6.Cyclic.signature_divides a b M).2.2
  apply hM
  simpa [hs] using hd

theorem M6.BoundaryFibers.kernel_card : ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = (0,0)} = 2^(M6.Cyclic.signature a b M).natDegree := by
  change ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = (0, 0)} = 2 ^ (M6.Cyclic.signature a b M).natDegree
  intro a b M hM
  simp_rw [M6.BoundaryFibers.kernel_iff]
  exact M6.BoundaryFibers.annihilator_general
    (M6.Cyclic.signature a b M) M
    (M6.BoundaryFibers.nonzero_monic _ (M6.BoundaryFibers.signature_nonzero a b M hM))
    (M6.Cyclic.signature_divides a b M).2.2 hM

theorem M6.BoundaryFibers.fiber_card : ∀ (a b M : M6.BoundaryFibers.BP), M ≠ 0 → ∀ h₀ : AdjoinRoot M, Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = M6.BoundaryFibers.boundary a b M h₀} = 2^(M6.Cyclic.signature a b M).natDegree := by
  change ∀ (a b M : M6.BoundaryFibers.BP), M ≠ 0 → ∀ h₀ : AdjoinRoot M, Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = M6.BoundaryFibers.boundary a b M h₀} = 2 ^ (M6.Cyclic.signature a b M).natDegree
  intro a b M hM h₀
  have hsub (h k : AdjoinRoot M) :
      M6.BoundaryFibers.boundary a b M (h - k) =
        M6.BoundaryFibers.boundary a b M h - M6.BoundaryFibers.boundary a b M k := by
    unfold M6.BoundaryFibers.boundary
    apply Prod.ext <;> exact mul_sub _ _ _
  let e : {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = (0, 0)} ≃
      {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = M6.BoundaryFibers.boundary a b M h₀} :=
    { toFun := fun h => ⟨h.val + h₀, by
        rw [M6.BoundaryFibers.boundary_add, h.property]
        exact zero_add _⟩
      invFun := fun h => ⟨h.val - h₀, by
        rw [hsub, h.property]
        exact sub_self _⟩
      left_inv := by
        intro h
        apply Subtype.ext
        exact add_sub_cancel_right h.val h₀
      right_inv := by
        intro h
        apply Subtype.ext
        exact sub_add_cancel h.val h₀ }
  exact (Nat.card_congr e.symm).trans (M6.BoundaryFibers.kernel_card a b M hM)

theorem M6.Flatten.flatten_add : ∀ (N : ℕ) (z w : M6.Physical.Word N), M6.Flatten.flatten N (z+w) = M6.Flatten.flatten N z + M6.Flatten.flatten N w := by
  change ∀ (N : ℕ) (z w : M6.Physical.Word N), M6.Flatten.flatten N (z + w) = M6.Flatten.flatten N z + M6.Flatten.flatten N w
  intro N z w
  funext i
  by_cases h : i.val < N <;> simp [M6.Flatten.flatten, h]

theorem M6.Flatten.flatten_dot : ∀ (N : ℕ) [NeZero N] (z w : M6.Physical.Word N), M6.Character.dot (M6.Flatten.flatten N z) (M6.Flatten.flatten N w) = M6.Physical.pairing N z w := by
  change ∀ (N : ℕ) [NeZero N] (z w : M6.Physical.Word N), M6.Character.dot (M6.Flatten.flatten N z) (M6.Flatten.flatten N w) = M6.Physical.pairing N z w
  intro N inst z w
  classical
  let e : Fin N ≃ ZMod N :=
    { toFun := fun i => (i.val : ZMod N)
      invFun := fun i => ⟨i.val, ZMod.val_lt i⟩
      left_inv := by
        intro i
        apply Fin.ext
        change ((i.val : ZMod N).val) = i.val
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.is_lt]
      right_inv := by
        intro i
        simp }
  have hsum (f : ZMod N → ZMod 2) :
      (∑ i : Fin N, f (i.val : ZMod N)) = ∑ i : ZMod N, f i :=
    e.sum_comp f
  have hleft (i : Fin N) : i.val < N := i.is_lt
  have hright (i : Fin N) : ¬ N + i.val < N := by omega
  unfold M6.Character.dot M6.Flatten.flatten M6.Physical.pairing M6.Physical.dot
  rw [two_mul, Fin.sum_univ_add]
  simpa [Fin.val_castAdd, Fin.val_natAdd, hleft, hright] using
    congrArg₂ (fun a b : ZMod 2 => a + b)
      (hsum (fun i => z.1 i * w.1 i))
      (hsum (fun i => z.2 i * w.2 i))

theorem M6.Flatten.flatten_left : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Flatten.unflatten N (M6.Flatten.flatten N z) = z := by
  intro N _ z
  apply Prod.ext
  · funext i
    have hi : i.val < N := ZMod.val_lt i
    simp [M6.Flatten.unflatten, M6.Flatten.flatten, hi]
  · funext i
    have hi : ¬ N + i.val < N := by omega
    simp [M6.Flatten.unflatten, M6.Flatten.flatten, hi, Nat.add_sub_cancel_left]

theorem M6.Flatten.flatten_right : ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Flatten.flatten N (M6.Flatten.unflatten N v) = v := by
  change ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2 * N)), M6.Flatten.flatten N (M6.Flatten.unflatten N v) = v
  intro N inst v
  funext i
  by_cases h : i.val < N
  · simp only [M6.Flatten.flatten, M6.Flatten.unflatten, if_pos h, dif_pos h]
    apply congrArg v
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt h]
  · have hi : i.val - N < N := by omega
    simp only [M6.Flatten.flatten, M6.Flatten.unflatten, if_neg h, dif_neg h]
    apply congrArg v
    apply Fin.ext
    simp only [Fin.val_mk, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    omega

theorem M6.Flatten.flatten_smul : ∀ (N : ℕ) (c : ZMod 2) (z : M6.Physical.Word N), M6.Flatten.flatten N (c • z) = c • M6.Flatten.flatten N z := by
  change ∀ (N : ℕ) (c : ZMod 2) (z : M6.Physical.Word N), M6.Flatten.flatten N (c • z) = c • M6.Flatten.flatten N z
  intro N c z
  funext i
  simp only [M6.Flatten.flatten, Pi.smul_apply]
  split <;> simp_all

theorem M6.Flatten.flatten_weight : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Pinned.weight (M6.Flatten.flatten N z) = M6.Physical.wordWeight N z := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Pinned.weight (M6.Flatten.flatten N z) = M6.Physical.wordWeight N z
  intro N inst z
  classical
  have hs (f : ZMod N → ℕ) :
      (∑ i : Fin N, f (i.val : ZMod N)) = ∑ x : ZMod N, f x := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n =>
      change (∑ i : ZMod (n + 1), f (i.val : ZMod (n + 1))) = _
      apply Finset.sum_congr rfl
      intro i _
      rw [ZMod.natCast_zmod_val]
  unfold M6.Pinned.weight M6.Flatten.flatten M6.Physical.wordWeight M6.Physical.weight
  simp only [Finset.card_filter]
  rw [show 2 * N = N + N by omega, Fin.sum_univ_add]
  apply congrArg₂ (fun a b : ℕ => a + b)
  · calc
      _ = ∑ i : Fin N, if z.1 (i.val : ZMod N) ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [Fin.is_lt]
      _ = _ := hs (fun x => if z.1 x ≠ 0 then 1 else 0)
  · calc
      _ = ∑ i : Fin N, if z.2 (i.val : ZMod N) ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : ¬ N + i.val < N := by omega
        simp [hi]
      _ = _ := hs (fun x => if z.2 x ≠ 0 then 1 else 0)

theorem M6.Flatten.J_involution : ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Flatten.J N (M6.Flatten.J N v) = v := by
  change ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2 * N)), M6.Flatten.J N (M6.Flatten.J N v) = v
  intro N inst v
  unfold M6.Flatten.J
  rw [M6.Flatten.flatten_left, M6.Physical.J_involution, M6.Flatten.flatten_right]

theorem M6.Flatten.J_weight : ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Pinned.weight (M6.Flatten.J N v) = M6.Pinned.weight v := by
  change ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2 * N)), M6.Pinned.weight (M6.Flatten.J N v) = M6.Pinned.weight v
  intro N inst v
  unfold M6.Flatten.J
  rw [M6.Flatten.flatten_weight, M6.Physical.J_weight,
    ← M6.Flatten.flatten_weight N (M6.Flatten.unflatten N v),
    M6.Flatten.flatten_right]

theorem M6.Flatten.cycle_orthogonal : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ↔ ∀ h : M6.Physical.Block N, M6.Character.dot (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))) v = 0 := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ↔ ∀ h : M6.Physical.Block N, M6.Character.dot (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))) v = 0
  intro N inst a b v
  simpa only [← M6.Flatten.flatten_dot, M6.Flatten.flatten_right] using
    (M6.Physical.cycle_orthogonal N a b (M6.Flatten.unflatten N v))

theorem M6.Spaces.boundary_eval : ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Spaces.boundary N a b h = M6.Flatten.flatten N (M6.Physical.boundary N a b h) := by
  intro N inst a b h
  rfl

theorem M6.Spaces.dual_boundary_eval : ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Spaces.dualBoundary N a b h = M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Spaces.dualBoundary N a b h = M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h
  rfl

theorem M6.Spaces.input_card : ∀ (N : ℕ) [NeZero N], Nat.card (M6.Physical.Block N) = 2^N := by
  intro N inst
  change Nat.card (ZMod N → ZMod 2) = 2 ^ N
  simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem M6.Spaces.boundary_words_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.boundaryWords N a b ↔ ∃ h : M6.Physical.Block N, M6.Flatten.flatten N (M6.Physical.boundary N a b h) = v := by
  intro N inst a b v
  classical
  simp [M6.Spaces.boundaryWords, M6.Character.subspaceWords, M6.Spaces.B,
    LinearMap.mem_range, M6.Spaces.boundary_eval]

theorem M6.Spaces.cycle_words_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v
  classical
  change v ∈ Finset.filter (M6.Character.Orthogonal (M6.Spaces.dualBoundary N a b).range) Finset.univ ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (∀ q, q ∈ (M6.Spaces.dualBoundary N a b).range → M6.Character.dot q v = 0) ↔ _
  rw [M6.Flatten.cycle_orthogonal]
  constructor
  · intro hv h
    exact hv _ ⟨h, rfl⟩
  · intro hv q hq
    obtain ⟨h, rfl⟩ := hq
    exact hv h

theorem M6.Spaces.boundaries_are_cycles : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Spaces.boundaryWords N a b ⊆ M6.Spaces.cycleWords N a b := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Spaces.boundaryWords N a b ⊆ M6.Spaces.cycleWords N a b
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v hv
  obtain ⟨h, rfl⟩ := (M6.Spaces.boundary_words_iff N a b v).mp hv
  apply (M6.Spaces.cycle_words_iff N a b _).mpr
  rw [M6.Flatten.flatten_left]
  exact M6.Physical.boundary_cycle N a b h

theorem M6.Spaces.dual_boundary_card : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (M6.Character.subspaceWords (M6.Spaces.D N a b)).card = (M6.Spaces.boundaryWords N a b).card := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (M6.Character.subspaceWords (M6.Spaces.D N a b)).card = (M6.Spaces.boundaryWords N a b).card
  intro N inst a b
  classical
  have hd (v : M6.Pinned.Vector (2*N)) :
      v ∈ M6.Character.subspaceWords (M6.Spaces.D N a b) ↔
        ∃ h : M6.Physical.Block N,
          M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)) = v := by
    simp [M6.Character.subspaceWords, M6.Spaces.D, LinearMap.mem_range,
      M6.Spaces.dual_boundary_eval]
  refine Finset.card_bij (fun v _ => M6.Flatten.J N v) ?_ ?_ ?_
  · intro v hv
    obtain ⟨h, rfl⟩ := (hd v).mp hv
    apply (M6.Spaces.boundary_words_iff N a b _).mpr
    refine ⟨h, ?_⟩
    simp [M6.Flatten.J, M6.Flatten.flatten_left, M6.Physical.J_involution]
  · intro v hv w hw he
    have hh := congrArg (M6.Flatten.J N) he
    simpa only [M6.Flatten.J_involution] using hh
  · intro v hv
    obtain ⟨h, rfl⟩ := (M6.Spaces.boundary_words_iff N a b v).mp hv
    refine ⟨M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)), ?_, ?_⟩
    · exact (hd _).mpr ⟨h, rfl⟩
    · simp [M6.Flatten.J, M6.Flatten.flatten_left, M6.Physical.J_involution]

theorem M6.Spaces.logical_words_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.logicalWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ∧ ¬ ∃ h : M6.Physical.Block N, M6.Flatten.flatten N (M6.Physical.boundary N a b h) = v := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.logicalWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ∧ ¬ ∃ h : M6.Physical.Block N, M6.Flatten.flatten N (M6.Physical.boundary N a b h) = v
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v
  classical
  simp only [M6.Spaces.logicalWords, Finset.mem_sdiff,
    M6.Spaces.cycle_words_iff, M6.Spaces.boundary_words_iff]

theorem M6.Spaces.zero_not_logical : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (0 : M6.Pinned.Vector (2*N)) ∉ M6.Spaces.logicalWords N a b := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (0 : M6.Pinned.Vector (2*N)) ∉ M6.Spaces.logicalWords N a b
  intro N inst a b
  classical
  have hz : (0 : M6.Pinned.Vector (2*N)) ∈ M6.Spaces.boundaryWords N a b := by
    simpa [M6.Spaces.boundaryWords, M6.Character.subspaceWords] using
      (M6.Spaces.B N a b).zero_mem
  simpa [M6.Spaces.logicalWords, Finset.mem_sdiff, hz]

theorem M6.Character.sign_add : ∀ (a b : ZMod 2), M6.Character.sign (a+b) = M6.Character.sign a * M6.Character.sign b := by
  change ∀ (a b : ZMod 2), M6.Character.sign (a + b) = M6.Character.sign a * M6.Character.sign b
  intro a b
  fin_cases a <;> fin_cases b <;> decide

theorem M6.Character.sign_eq_one : ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0) := by
  change ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0)
  intro a
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl <;> norm_num [M6.Character.sign, ZMod.val_zero, ZMod.val_one_eq_one_mod]

theorem M6.Character.character_add : ∀ (m : ℕ) (q r z : M6.Character.Vector m), M6.Character.character (q+r) z = M6.Character.character q z * M6.Character.character r z := by
  change ∀ (m : ℕ) (q r z : M6.Character.Vector m), M6.Character.character (q + r) z = M6.Character.character q z * M6.Character.character r z
  intro m q r z
  simp only [M6.Character.character, M6.Character.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib, M6.Character.sign_add]

theorem M6.Character.sign_sum : ∀ (m : ℕ) (f : Fin m → ZMod 2), M6.Character.sign (∑ i, f i) = ∏ i, M6.Character.sign (f i) := by
  change ∀ (m : ℕ) (f : Fin m → ZMod 2), M6.Character.sign (∑ i, f i) = ∏ i, M6.Character.sign (f i)
  intro m f
  have h : ∀ s : Finset (Fin m), M6.Character.sign (∑ i ∈ s, f i) = ∏ i ∈ s, M6.Character.sign (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, Finset.prod_empty]
        decide
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, M6.Character.sign_add, ih]
  exact h Finset.univ

theorem M6.Character.character_product : ∀ (m : ℕ) (q z : M6.Character.Vector m), M6.Character.character q z = ∏ i, M6.Character.sign (q i * z i) := by
  change ∀ (m : ℕ) (q z : M6.Character.Vector m), M6.Character.character q z = ∏ i, M6.Character.sign (q i * z i)
  intro m q z
  change M6.Character.sign (∑ i, q i * z i) = ∏ i, M6.Character.sign (q i * z i)
  exact M6.Character.sign_sum m (fun i => q i * z i)

theorem M6.Character.orthogonality : ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (z : M6.Character.Vector m), M6.Character.characterSum D z = M6.Character.orthogonalIndicator D z := by
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (z : M6.Character.Vector m), M6.Character.characterSum D z = M6.Character.orthogonalIndicator D z
  intro m D z
  classical
  have mem_words (q : M6.Character.Vector m) : q ∈ M6.Character.subspaceWords D ↔ q ∈ D := by
    simp [M6.Character.subspaceWords]
  unfold M6.Character.orthogonalIndicator
  by_cases h : M6.Character.Orthogonal D z
  · rw [if_pos h]
    have hc : ∀ q ∈ M6.Character.subspaceWords D, M6.Character.character q z = 1 := by
      intro q hq
      apply (M6.Character.sign_eq_one _).1.mpr
      exact h q ((mem_words q).mp hq)
    unfold M6.Character.characterSum
    calc
      ∑ q ∈ M6.Character.subspaceWords D, M6.Character.character q z =
          ∑ q ∈ M6.Character.subspaceWords D, (1 : ℤ) := Finset.sum_congr rfl hc
      _ = _ := by simp
  · rw [if_neg h]
    unfold M6.Character.Orthogonal at h
    push_neg at h
    obtain ⟨q0, hq0, hne⟩ := h
    have hs : M6.Character.character q0 z = -1 :=
      (M6.Character.sign_eq_one _).2.mpr hne
    have ht : (∑ q ∈ M6.Character.subspaceWords D, M6.Character.character (q0 + q) z) =
        ∑ q ∈ M6.Character.subspaceWords D, M6.Character.character q z := by
      refine Finset.sum_bij (fun q _ => q0 + q) ?_ ?_ ?_ ?_
      · intro q hq
        exact (mem_words _).mpr (D.add_mem hq0 ((mem_words q).mp hq))
      · intro q hq r hr heq
        exact add_left_cancel heq
      · intro q hq
        refine ⟨q - q0, (mem_words _).mpr (D.sub_mem ((mem_words q).mp hq) hq0), ?_⟩
        abel
      · intro q hq
        rfl
    simp only [M6.Character.character_add, hs, neg_one_mul, Finset.sum_neg_distrib] at ht
    unfold M6.Character.characterSum
    omega

theorem M6.Character.weighted_factorization : ∀ (m : ℕ) (w : Fin m → ZMod 2 → Polynomial ℤ) (q : M6.Character.Vector m), M6.Character.localTransform w q = ∑ z : M6.Character.Vector m, Polynomial.C (M6.Character.character q z) * ∏ i, w i (z i) := by
  change ∀ (m : ℕ) (w : Fin m → ZMod 2 → Polynomial ℤ) (q : M6.Character.Vector m), M6.Character.localTransform w q = ∑ z : M6.Character.Vector m, Polynomial.C (M6.Character.character q z) * ∏ i, w i (z i)
  intro m w q
  classical
  unfold M6.Character.localTransform
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [M6.Character.character_product, map_prod, Finset.prod_mul_distrib, mul_comm]

theorem M6.Character.weighted_macwilliams : ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (w : Fin m → ZMod 2 → Polynomial ℤ), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Character.weightedDual D w = M6.Character.weightedTransform D w := by
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (w : Fin m → ZMod 2 → Polynomial ℤ), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Character.weightedDual D w = M6.Character.weightedTransform D w
  intro m D w
  classical
  symm
  calc
    M6.Character.weightedTransform D w =
        ∑ z : M6.Character.Vector m, Polynomial.C (M6.Character.characterSum D z) * ∏ i, w i (z i) := by
      unfold M6.Character.weightedTransform
      simp_rw [M6.Character.weighted_factorization]
      rw [Finset.sum_comm]
      simp only [M6.Character.characterSum, map_sum, Finset.sum_mul]
    _ = Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Character.weightedDual D w := by
      simp only [M6.Character.orthogonality, M6.Character.orthogonalIndicator,
        M6.Character.weightedDual, M6.Character.dualWords,
        Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : M6.Character.Orthogonal D z <;> simp [h]

theorem M6.Character.free_character_factor : ∀ (m : ℕ) (i : Fin m) (s : ZMod 2), M6.Character.pinnedCharacterFactor (M6.Pinned.free m) i s = 1 + Polynomial.C (M6.Character.sign s) * Polynomial.X := by
  change ∀ (m : ℕ) (i : Fin m) (s : ZMod 2), M6.Character.pinnedCharacterFactor (M6.Pinned.free m) i s = 1 + Polynomial.C (M6.Character.sign s) * Polynomial.X
  intro m i s
  classical
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hv : (1 : ZMod 2).val = 1 := rfl
  simp [M6.Character.pinnedCharacterFactor, M6.Character.boundaryFactor,
    M6.Pinned.free, h, M6.Character.sign, hv]

theorem M6.Character.weight_as_sum : ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val := by
  change ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
  intro m v
  classical
  unfold M6.Pinned.weight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  generalize hx : v i = x
  have hx01 : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx01 with rfl | rfl <;> norm_num [ZMod.val_zero, ZMod.val_one_eq_one_mod]

theorem M6.Character.pinned_product : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Character.Vector m), (∏ i, M6.Character.boundaryFactor P i (v i)) = M6.Character.pinnedMonomial P v := by
  change ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Character.Vector m), (∏ i, M6.Character.boundaryFactor P i (v i)) = M6.Character.pinnedMonomial P v
  intro m P v
  classical
  by_cases h : M6.Pinned.agrees P v
  · rw [M6.Character.pinnedMonomial, if_pos h]
    have hf : ∀ i, M6.Character.boundaryFactor P i (v i) = (Polynomial.X : Polynomial ℤ) ^ (v i).val := by
      intro i
      unfold M6.Pinned.agrees at h
      have hi := h i
      cases hp : P i <;> simp_all [M6.Character.boundaryFactor]
    simp_rw [hf]
    rw [M6.Character.weight_as_sum]
    have hp : ∀ s : Finset (Fin m), (∏ i ∈ s, (Polynomial.X : Polynomial ℤ) ^ (v i).val) = Polynomial.X ^ (∑ i ∈ s, (v i).val) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simp [hi, ih, pow_add]
    exact hp Finset.univ
  · rw [M6.Character.pinnedMonomial, if_neg h]
    by_contra hn
    apply h
    unfold M6.Pinned.agrees
    intro i
    have hi := Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i)
    cases hp : P i <;> simp [M6.Character.boundaryFactor, hp] at hi ⊢ <;> aesop

theorem M6.Character.pinned_macwilliams : ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (P : M6.Pinned.Pins m), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Pinned.enumerator (M6.Character.dualWords D) P = M6.Character.pinnedTransform D P := by
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (P : M6.Pinned.Pins m), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Pinned.enumerator (M6.Character.dualWords D) P = M6.Character.pinnedTransform D P
  intro m D P
  classical
  simpa [M6.Character.weightedDual, M6.Character.weightedTransform,
    M6.Character.localTransform, M6.Character.pinnedTransform,
    M6.Character.pinnedCharacterFactor, M6.Character.pinned_product,
    M6.Character.pinnedMonomial, M6.Pinned.enumerator, Finset.sum_filter]
    using M6.Character.weighted_macwilliams m D (M6.Character.boundaryFactor P)

theorem M6.Character.constant_transform : ∀ (m : ℕ) (q : M6.Character.Vector m), (q = 0 → M6.Character.localTransform (fun _ _ => (1 : Polynomial ℤ)) q = Polynomial.C ((2 : ℤ)^m)) ∧ (q ≠ 0 → M6.Character.localTransform (fun _ _ => (1 : Polynomial ℤ)) q = 0) := by
  classical
  change ∀ (m : ℕ) (q : M6.Character.Vector m), _
  intro m q
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hz : M6.Character.sign 0 = 1 :=
    ((M6.Character.sign_eq_one 0).1).2 rfl
  have hs (a : ZMod 2) :
      (∑ b : ZMod 2, Polynomial.C (M6.Character.sign (a * b)) * (1 : Polynomial ℤ)) =
        if a = 0 then 2 else 0 := by
    by_cases ha : a = 0
    · subst a
      simp [hu, hz]
    · have hn : M6.Character.sign a = -1 :=
        ((M6.Character.sign_eq_one a).2).2 ha
      simp [hu, hz, hn, ha]
  constructor
  · intro hq
    subst q
    simp only [M6.Character.localTransform, hs]
    simp
  · intro hq
    have hi : ∃ i : Fin m, q i ≠ 0 := by
      by_contra h
      apply hq
      funext i
      simpa using (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hi
    unfold M6.Character.localTransform
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hs, if_neg hi]

theorem M6.FiberSum.sum_by_fibers : ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = M6.FiberSum.fiberSum L w := by
  classical
  change ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = M6.FiberSum.fiberSum L w
  intro α β _ _ L w
  simpa [M6.FiberSum.pullbackSum, M6.FiberSum.fiberSum, M6.FiberSum.fiber,
    Fintype.card_subtype, nsmul_eq_mul] using (Fintype.sum_fiberwise' L w).symm

theorem M6.Character.dual_cardinality : ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)), (M6.Character.subspaceWords D).card * (M6.Character.dualWords D).card = 2^m := by
  classical
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)), _
  intro m D
  have hz : (0 : M6.Character.Vector m) ∈ M6.Character.subspaceWords D := by
    simp [M6.Character.subspaceWords]
  have hd : M6.Character.weightedDual D (fun _ _ => (1 : Polynomial ℤ)) =
      Polynomial.C ((M6.Character.dualWords D).card : ℤ) := by
    simp [M6.Character.weightedDual]
  have ht : M6.Character.weightedTransform D (fun _ _ => (1 : Polynomial ℤ)) =
      Polynomial.C ((2 : ℤ)^m) := by
    unfold M6.Character.weightedTransform
    rw [Finset.sum_eq_single (0 : M6.Character.Vector m)]
    · exact (M6.Character.constant_transform m 0).1 rfl
    · intro q hq hq0
      exact (M6.Character.constant_transform m q).2 hq0
    · intro h
      exact (h hz).elim
  have h := M6.Character.weighted_macwilliams m D (fun _ _ => (1 : Polynomial ℤ))
  rw [hd, ht, ← map_mul] at h
  have hi := Polynomial.C_injective h
  exact_mod_cast hi

theorem M6.FiberSum.uniform_weighted_sum : ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → ∀ (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = Polynomial.C (k : ℤ) * ∑ b, w b := by
  classical
  change ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → ∀ (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = Polynomial.C (k : ℤ) * ∑ b, w b
  intro α β _ _ L k h w
  change ∀ b, (M6.FiberSum.fiber L b).card = k at h
  rw [M6.FiberSum.sum_by_fibers α β L w]
  simp only [M6.FiberSum.fiberSum, h, Finset.mul_sum]

theorem M6.FiberSum.uniform_cardinality : ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → Fintype.card α = k * Fintype.card β := by
  classical
  change ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → Fintype.card α = k * Fintype.card β
  intro α β _ _ L k h
  change ∀ b, (M6.FiberSum.fiber L b).card = k at h
  have hc : ∀ b, Fintype.card {a : α // L a = b} = k := by
    intro b
    simpa [Fintype.card_subtype, M6.FiberSum.fiber] using h b
  have hs := (Fintype.sum_fiberwise' L (fun _ : β => (1 : ℕ))).symm
  simpa [hc, Nat.mul_comm] using hs

theorem M6.Pinned.agrees_pin : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Pinned.Vector m) (i : Fin m) (b : ZMod 2), P i = none → (M6.Pinned.agrees (M6.Pinned.pin P i b) v ↔ M6.Pinned.agrees P v ∧ v i = b) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Pinned.Vector m) (i : Fin m) (b : ZMod 2), P i = none → (M6.Pinned.agrees (M6.Pinned.pin P i b) v ↔ M6.Pinned.agrees P v ∧ v i = b)
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro m P v i b hP
  unfold M6.Pinned.agrees
  constructor
  · intro h
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simp [hP]
      · simpa [M6.Pinned.pin, Function.update, hji, Ne.symm hji] using h j
    · simpa [M6.Pinned.pin, Function.update] using h i
  · rintro ⟨h, hv⟩ j
    by_cases hji : j = i
    · subst j
      simp [M6.Pinned.pin, Function.update, hv]
    · simpa [M6.Pinned.pin, Function.update, hji, Ne.symm hji] using h j

theorem M6.Pinned.choose_properties : ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (i : Fin m), M6.Pinned.refines P (M6.Pinned.choose c P i).1 ∧ (M6.Pinned.choose c P i).1 i ≠ none ∧ (M6.Pinned.choose c P i).2 ≤ 1 := by
  classical
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (i : Fin m), M6.Pinned.refines P (M6.Pinned.choose c P i).1 ∧ (M6.Pinned.choose c P i).1 i ≠ none ∧ (M6.Pinned.choose c P i).2 ≤ 1
  intro m c P i
  cases h : P i with
  | none =>
      have hr (b : ZMod 2) : M6.Pinned.refines P (M6.Pinned.pin P i b) := by
        unfold M6.Pinned.refines
        intro j
        by_cases hj : j = i
        · subst j
          simp [h]
        · simp [M6.Pinned.pin, hj]
      have hn (b : ZMod 2) : M6.Pinned.pin P i b i ≠ none := by
        simp [M6.Pinned.pin]
      simp only [M6.Pinned.choose, h]
      split <;> simp_all
  | some b =>
      simp [M6.Pinned.choose, h, M6.Pinned.refines]

theorem M6.Pinned.count_nonnegative_positive : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), 0 ≤ M6.Pinned.count L P d ∧ (0 < M6.Pinned.count L P d ↔ ∃ v ∈ L, M6.Pinned.agrees P v ∧ M6.Pinned.weight v = d) := by
  classical
  intro m L P d
  unfold M6.Pinned.count
  constructor
  · exact Int.natCast_nonneg _
  · simp [Int.natCast_pos, Finset.card_pos, Finset.Nonempty, and_assoc]

theorem M6.Pinned.decode_unique : ∀ (m : ℕ) (P : M6.Pinned.Pins m), M6.Pinned.assigned P → ∀ v : M6.Pinned.Vector m, (M6.Pinned.agrees P v ↔ v = M6.Pinned.decode P) := by
  intro m P hP v
  unfold M6.Pinned.assigned at hP
  constructor
  · intro hv
    unfold M6.Pinned.agrees at hv
    funext i
    have ha := hP i
    have hv' := hv i
    cases hi : P i <;> simp_all [M6.Pinned.decode]
  · intro hv
    subst v
    unfold M6.Pinned.agrees
    intro i
    cases hi : P i <;> simp [M6.Pinned.decode, hi]

theorem M6.Pinned.distance_spec : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), (M6.Pinned.distance L = none ↔ L = ∅) ∧ ∀ d : ℕ, (M6.Pinned.distance L = some d ↔ (∃ v ∈ L, M6.Pinned.weight v = d) ∧ ∀ v ∈ L, d ≤ M6.Pinned.weight v) := by
  classical
  intro m L
  by_cases h : L.Nonempty
  · have hi : (L.image M6.Pinned.weight).Nonempty := h.image M6.Pinned.weight
    constructor
    · simp [M6.Pinned.distance, h, h.ne_empty]
    · intro d
      change (if h : L.Nonempty then
        some ((L.image M6.Pinned.weight).min' (h.image M6.Pinned.weight))
        else none) = some d ↔ _
      rw [dif_pos h, Option.some.injEq]
      constructor
      · intro hd
        obtain ⟨v, hv, hw⟩ := Finset.mem_image.mp
          (Finset.min'_mem (L.image M6.Pinned.weight) hi)
        constructor
        · exact ⟨v, hv, hw.trans hd⟩
        · intro w hw
          rw [← hd]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
      · rintro ⟨⟨v, hv, hvd⟩, hleast⟩
        apply le_antisymm
        · rw [← hvd]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        · obtain ⟨w, hw, hweight⟩ := Finset.mem_image.mp
            (Finset.min'_mem (L.image M6.Pinned.weight) hi)
          rw [← hweight]
          exact hleast w hw
  · have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst L
    simp [M6.Pinned.distance]

theorem M6.Pinned.enumerator_coeff : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), (M6.Pinned.enumerator L P).coeff d = M6.Pinned.count L P d := by
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), (M6.Pinned.enumerator L P).coeff d = M6.Pinned.count L P d
  intro m L P d
  classical
  simp only [M6.Pinned.enumerator, M6.Pinned.count,
    Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hrev : (d = M6.Pinned.weight v) ↔ (M6.Pinned.weight v = d) := eq_comm
  by_cases ha : M6.Pinned.agrees P v <;>
    by_cases hw : M6.Pinned.weight v = d <;>
    simp [ha, hw, Polynomial.coeff_X_pow, eq_comm]
  all_goals omega

theorem M6.Pinned.recover_positive : ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ), M6.Pinned.partitions c → ∀ (P : M6.Pinned.Pins m) (xs : List (Fin m)), 0 < c P → 0 < c (M6.Pinned.recover c P xs).1 := by
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ), M6.Pinned.partitions c → ∀ (P : M6.Pinned.Pins m) (xs : List (Fin m)), 0 < c P → 0 < c (M6.Pinned.recover c P xs).1
  intro m c hc
  unfold M6.Pinned.partitions at hc
  have hchoose : ∀ (P : M6.Pinned.Pins m) (i : Fin m), 0 < c P → 0 < c (M6.Pinned.choose c P i).1 := by
    intro P i hP
    unfold M6.Pinned.choose
    split
    all_goals
      first
      | exact hP
      | (split <;> dsimp only <;>
          first
          | assumption
          | (have hsum := hc P i (by assumption)
             omega))
  intro P xs
  induction xs generalizing P with
  | nil =>
      simpa only [M6.Pinned.recover] using (fun h : 0 < c P => h)
  | cons i xs ih =>
      intro hP
      simpa only [M6.Pinned.recover] using
        (ih (M6.Pinned.choose c P i).1 (hchoose P i hP))

theorem M6.Pinned.weight_bound : ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m := by
  change ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m
  intro m v
  classical
  unfold M6.Pinned.weight
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = m := by simp

theorem M6.Pinned.count_pin_partition : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ), M6.Pinned.partitions (fun P => M6.Pinned.count L P d) := by
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ), M6.Pinned.partitions (fun P => M6.Pinned.count L P d)
  classical
  intro m L d
  unfold M6.Pinned.partitions
  intro P i hP
  have hbits : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  induction L using Finset.induction_on with
  | empty =>
      simp [M6.Pinned.count, M6.Pinned.enumerator]
  | @insert v L hv ih =>
      rcases hbits (v i) with hb | hb <;>
        by_cases ha : M6.Pinned.agrees P v <;>
        by_cases hw : M6.Pinned.weight v = d <;>
        simp_all [M6.Pinned.count, M6.Pinned.enumerator,
          M6.Pinned.agrees_pin, Finset.filter_insert,
          Finset.sum_insert, Polynomial.coeff_sum,
          Polynomial.coeff_monomial] <;> omega

theorem M6.Pinned.first_positive_distance : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), M6.Pinned.firstPositive m (M6.Pinned.enumerator L (M6.Pinned.free m)) = M6.Pinned.distance L := by
  classical
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), M6.Pinned.firstPositive m (M6.Pinned.enumerator L (M6.Pinned.free m)) = M6.Pinned.distance L
  intro m L
  have hc : ∀ d : ℕ, (0 < (M6.Pinned.enumerator L (M6.Pinned.free m)).coeff d) ↔ ∃ v ∈ L, M6.Pinned.weight v = d := by
    intro d
    rw [M6.Pinned.enumerator_coeff]
    simpa [M6.Pinned.agrees, M6.Pinned.free] using
      (M6.Pinned.count_nonnegative_positive m L (M6.Pinned.free m) d).2
  cases hd : M6.Pinned.distance L with
  | none =>
      have he : L = ∅ := (M6.Pinned.distance_spec m L).1.mp hd
      simp [M6.Pinned.firstPositive, he, M6.Pinned.enumerator]
  | some d =>
      obtain ⟨hwitness, hleast⟩ := (M6.Pinned.distance_spec m L).2 d |>.mp hd
      have hbound : d < m + 1 := by
        obtain ⟨v, hv, hweight⟩ := hwitness
        have hb := M6.Pinned.weight_bound m v
        omega
      have hn : ∀ j < d, ¬ ∃ v ∈ L, M6.Pinned.weight v = j := by
        intro j hj
        rintro ⟨v, hv, hw⟩
        have hl := hleast v hv
        omega
      simp only [M6.Pinned.firstPositive, List.find?_range_eq_some, decide_eq_true_eq, List.mem_range, hc]
      refine ⟨hwitness, hbound, ?_⟩
      intro j hj
      simpa using hn j hj

theorem M6.Pinned.recover_properties : ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (xs : List (Fin m)), M6.Pinned.refines P (M6.Pinned.recover c P xs).1 ∧ (∀ i ∈ xs, (M6.Pinned.recover c P xs).1 i ≠ none) ∧ (M6.Pinned.recover c P xs).2 ≤ xs.length := by
  classical
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (xs : List (Fin m)), M6.Pinned.refines P (M6.Pinned.recover c P xs).1 ∧ (∀ i ∈ xs, (M6.Pinned.recover c P xs).1 i ≠ none) ∧ (M6.Pinned.recover c P xs).2 ≤ xs.length
  intro m c P xs
  have trans_refines (A B C : M6.Pinned.Pins m)
      (hAB : M6.Pinned.refines A B) (hBC : M6.Pinned.refines B C) :
      M6.Pinned.refines A C := by
    unfold M6.Pinned.refines at hAB hBC ⊢
    intro j b hj
    exact hBC j b (hAB j b hj)
  have preserve (A B : M6.Pinned.Pins m)
      (hAB : M6.Pinned.refines A B) (j : Fin m)
      (hj : A j ≠ none) : B j ≠ none := by
    unfold M6.Pinned.refines at hAB
    cases h : A j with
    | none => exact False.elim (hj h)
    | some b =>
        rw [hAB j b h]
        simp
  induction xs generalizing P with
  | nil =>
      simp [M6.Pinned.recover, M6.Pinned.refines]
  | cons i xs ih =>
      have hcprop := M6.Pinned.choose_properties m c P i
      cases hc : M6.Pinned.choose c P i with
      | mk Q k =>
          have hrprop := ih Q
          cases hr : M6.Pinned.recover c Q xs with
          | mk R n =>
              simp only [hc, Prod.fst, Prod.snd] at hcprop
              simp only [hr, Prod.fst, Prod.snd] at hrprop
              simp only [M6.Pinned.recover, hc, hr, Prod.fst, Prod.snd]
              refine ⟨trans_refines P Q R hcprop.1 hrprop.1, ?_, ?_⟩
              · intro j hj
                rcases List.mem_cons.mp hj with hji | hj
                · rw [hji]
                  exact preserve Q R hrprop.1 i hcprop.2.1
                · exact hrprop.2.1 j hj
              · have hk := hcprop.2.2
                have hn := hrprop.2.2
                simp only [List.length_cons]
                omega

theorem M6.Pinned.recover_from_counts : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ) (c : M6.Pinned.Pins m → ℤ), (∀ P, c P = M6.Pinned.count L P d) → 0 < c (M6.Pinned.free m) → let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m); M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (d : ℕ) (c : M6.Pinned.Pins m → ℤ), (∀ P, c P = M6.Pinned.count L P d) → 0 < c (M6.Pinned.free m) → let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m); M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro m L d c hc hpos
  let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m)
  change M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m
  have heq : c = fun P => M6.Pinned.count L P d := funext hc
  have hpart : M6.Pinned.partitions c := by
    rw [heq]
    exact M6.Pinned.count_pin_partition m L d
  have hp := M6.Pinned.recover_positive m c hpart (M6.Pinned.free m) (List.finRange m) hpos
  change 0 < c r.1 at hp
  rw [hc r.1] at hp
  have hr := M6.Pinned.recover_properties m c (M6.Pinned.free m) (List.finRange m)
  have ha : M6.Pinned.assigned r.1 := by
    intro i
    exact hr.2.1 i (by simp)
  obtain ⟨v, hvL, hvA, hvW⟩ := (M6.Pinned.count_nonnegative_positive m L r.1 d).2.mp hp
  have hv : v = M6.Pinned.decode r.1 := (M6.Pinned.decode_unique m r.1 ha v).mp hvA
  refine ⟨hv ▸ hvL, hv ▸ hvW, ?_⟩
  simpa only [List.length_finRange] using hr.2.2

theorem M6.Pinned.solve_exact : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (Q : M6.Pinned.Pins m → Polynomial ℤ), (∀ P, Q P = M6.Pinned.enumerator L P) → (M6.Pinned.solve Q = none ↔ L = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve Q = some (d, v, k) → v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (Q : M6.Pinned.Pins m → Polynomial ℤ), (∀ P, Q P = M6.Pinned.enumerator L P) → (M6.Pinned.solve Q = none ↔ L = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve Q = some (d, v, k) → v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro m L Q hQ
  have hf : M6.Pinned.firstPositive m (Q (M6.Pinned.free m)) = M6.Pinned.distance L := by
    rw [hQ]
    exact M6.Pinned.first_positive_distance m L
  cases hd : M6.Pinned.distance L with
  | none =>
      have he : L = ∅ := (M6.Pinned.distance_spec m L).1.mp hd
      have hs : M6.Pinned.solve Q = none := by
        simp [M6.Pinned.solve, hf, hd]
      simp [hs, he]
  | some d =>
      obtain ⟨hwitness, hleast⟩ := (M6.Pinned.distance_spec m L).2 d |>.mp hd
      have hn : L ≠ ∅ := by
        intro he
        have hh := (M6.Pinned.distance_spec m L).1.mpr he
        rw [hd] at hh
        cases hh
      let c : M6.Pinned.Pins m → ℤ := fun P => (Q P).coeff d
      have hc : ∀ P, c P = M6.Pinned.count L P d := by
        intro P
        dsimp [c]
        rw [hQ, M6.Pinned.enumerator_coeff]
      have hp : 0 < c (M6.Pinned.free m) := by
        rw [hc]
        apply (M6.Pinned.count_nonnegative_positive m L (M6.Pinned.free m) d).2.mpr
        obtain ⟨v, hv, hw⟩ := hwitness
        exact ⟨v, hv, by simp [M6.Pinned.agrees, M6.Pinned.free], hw⟩
      let r := M6.Pinned.recover c (M6.Pinned.free m) (List.finRange m)
      have hr := M6.Pinned.recover_from_counts m L d c hc hp
      change M6.Pinned.decode r.1 ∈ L ∧ M6.Pinned.weight (M6.Pinned.decode r.1) = d ∧ r.2 ≤ m at hr
      have hs : M6.Pinned.solve Q = some (d, M6.Pinned.decode r.1, r.2) := by
        simp [M6.Pinned.solve, hf, hd, r, c]
      constructor
      · simp [hs, hn]
      · intro d' v k h
        have he := hs.symm.trans h
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl, rfl⟩
        exact ⟨hr.1, hr.2.1, hleast, hr.2.2⟩

theorem M6.Pinned.minimum_witness : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), L.Nonempty → ∃ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve (M6.Pinned.enumerator L) = some (d, v, k) ∧ v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), L.Nonempty → ∃ (d : ℕ) (v : M6.Pinned.Vector m) (k : ℕ), M6.Pinned.solve (M6.Pinned.enumerator L) = some (d, v, k) ∧ v ∈ L ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ L, d ≤ M6.Pinned.weight u) ∧ k ≤ m
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro m L hL
  have hspec := M6.Pinned.solve_exact m L (M6.Pinned.enumerator L) (fun P => rfl)
  cases hs : M6.Pinned.solve (M6.Pinned.enumerator L) with
  | none =>
      exact False.elim (hL.ne_empty (hspec.1.mp hs))
  | some result =>
      rcases result with ⟨d, v, k⟩
      exact ⟨d, v, k, rfl, hspec.2 d v k hs⟩

theorem M6.CSS.involution_distance : ∀ (m : ℕ) (LX LZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ LX ↔ J v ∈ LZ) → M6.Pinned.distance LX = M6.Pinned.distance LZ := by
  classical
  change ∀ (m : ℕ) (LX LZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ LX ↔ J v ∈ LZ) → M6.Pinned.distance LX = M6.Pinned.distance LZ
  intro m LX LZ J hJ hw hmem
  have hback (v : M6.CSS.Vector m) (hv : v ∈ LZ) : J v ∈ LX := by
    apply (hmem (J v)).mpr
    simpa only [hJ v] using hv
  cases hd : M6.Pinned.distance LX with
  | none =>
      have hX : LX = ∅ := (M6.Pinned.distance_spec m LX).1.mp hd
      have hZ : LZ = ∅ := by
        apply Finset.ext
        intro v
        constructor
        · intro hv
          have hx := hback v hv
          rw [hX] at hx
          simp at hx
        · intro hv
          simp at hv
      exact ((M6.Pinned.distance_spec m LZ).1.mpr hZ).symm
  | some d =>
      obtain ⟨⟨v, hv, hvw⟩, hmin⟩ := (M6.Pinned.distance_spec m LX).2 d |>.mp hd
      symm
      apply (M6.Pinned.distance_spec m LZ).2 d |>.mpr
      constructor
      · exact ⟨J v, (hmem v).mp hv, (hw v).trans hvw⟩
      · intro u hu
        have h := hmin (J u) (hback u hu)
        simpa only [hw u] using h

theorem M6.CSS.logical_pauli_components : ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (p : M6.CSS.Pauli m), p ∈ M6.CSS.logicalPaulis BX CX BZ CZ ↔ p.1 ∈ CX ∧ p.2 ∈ CZ ∧ (p.1 ∈ M6.CSS.logical BX CX ∨ p.2 ∈ M6.CSS.logical BZ CZ) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (p : M6.CSS.Pauli m), p ∈ M6.CSS.logicalPaulis BX CX BZ CZ ↔ p.1 ∈ CX ∧ p.2 ∈ CZ ∧ (p.1 ∈ M6.CSS.logical BX CX ∨ p.2 ∈ M6.CSS.logical BZ CZ)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ p
  classical
  simp only [M6.CSS.logicalPaulis, M6.CSS.logical, Finset.mem_filter,
    Finset.mem_product, Finset.mem_sdiff] <;> tauto

theorem M6.CSS.pure_weights : ∀ (m : ℕ) (v : M6.CSS.Vector m), M6.CSS.weight (v, 0) = M6.Pinned.weight v ∧ M6.CSS.weight (0, v) = M6.Pinned.weight v := by
  change ∀ (m : ℕ) (v : M6.CSS.Vector m), M6.CSS.weight (v, 0) = M6.Pinned.weight v ∧ M6.CSS.weight (0, v) = M6.Pinned.weight v
  intro m v
  classical
  simp [M6.CSS.weight, M6.CSS.support, M6.Pinned.weight]

theorem M6.CSS.quantum_distance_spec : ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (M6.CSS.quantumDistance BX CX BZ CZ = none ↔ M6.CSS.logicalPaulis BX CX BZ CZ = ∅) ∧ ∀ d : ℕ, (M6.CSS.quantumDistance BX CX BZ CZ = some d ↔ (∃ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, M6.CSS.weight p = d) ∧ ∀ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, d ≤ M6.CSS.weight p) := by
  classical
  intro m BX CX BZ CZ
  let L := M6.CSS.logicalPaulis BX CX BZ CZ
  have hdef : M6.CSS.logicalPaulis BX CX BZ CZ = L := rfl
  by_cases hL : L.Nonempty
  · have hs : (L.image M6.CSS.weight).Nonempty := hL.image M6.CSS.weight
    have hne : L ≠ ∅ := hL.ne_empty
    have hsne : L.image M6.CSS.weight ≠ ∅ := hs.ne_empty
    have hmin : ∀ d : ℕ,
        (L.image M6.CSS.weight).min' hs = d ↔
          (∃ p ∈ L, M6.CSS.weight p = d) ∧
            ∀ p ∈ L, d ≤ M6.CSS.weight p := by
      intro d
      constructor
      · intro hd
        subst d
        obtain ⟨p, hp, hw⟩ := Finset.mem_image.mp
          (Finset.min'_mem (L.image M6.CSS.weight) hs)
        refine ⟨⟨p, hp, hw⟩, ?_⟩
        intro q hq
        exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      · rintro ⟨⟨p, hp, hw⟩, hb⟩
        apply le_antisymm
        · rw [← hw]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
        · obtain ⟨q, hq, hqw⟩ := Finset.mem_image.mp
            (Finset.min'_mem (L.image M6.CSS.weight) hs)
          rw [← hqw]
          exact hb q hq
    simp [M6.CSS.quantumDistance, hdef, hL, hs, hne, hsne, hmin]
  · have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    simp [M6.CSS.quantumDistance, hdef, he]

theorem M6.CSS.support_bounds : ∀ (m : ℕ) (p : M6.CSS.Pauli m), M6.Pinned.weight p.1 ≤ M6.CSS.weight p ∧ M6.Pinned.weight p.2 ≤ M6.CSS.weight p := by
  change ∀ (m : ℕ) (p : M6.CSS.Pauli m), M6.Pinned.weight p.1 ≤ M6.CSS.weight p ∧ M6.Pinned.weight p.2 ≤ M6.CSS.weight p
  intro m p
  classical
  unfold M6.Pinned.weight M6.CSS.weight M6.CSS.support
  constructor
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inl hi
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inr hi

theorem M6.CSS.css_distance_min : ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → M6.CSS.quantumDistance BX CX BZ CZ = M6.CSS.minDistance (M6.Pinned.distance (M6.CSS.logical BX CX)) (M6.Pinned.distance (M6.CSS.logical BZ CZ)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → M6.CSS.quantumDistance BX CX BZ CZ = M6.CSS.minDistance (M6.Pinned.distance (M6.CSS.logical BX CX)) (M6.Pinned.distance (M6.CSS.logical BZ CZ))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ hBX hBZ hBCX hBCZ
  classical
  have pureX (v : M6.CSS.Vector m) (hv : v ∈ M6.CSS.logical BX CX) :
      (v, 0) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (v, 0)).mpr
    exact ⟨(Finset.mem_sdiff.mp hv).1, hBCZ hBZ, Or.inl hv⟩
  have pureZ (v : M6.CSS.Vector m) (hv : v ∈ M6.CSS.logical BZ CZ) :
      (0, v) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (0, v)).mpr
    exact ⟨hBCX hBX, (Finset.mem_sdiff.mp hv).1, Or.inr hv⟩
  have lower (d : ℕ)
      (hx : ∀ v ∈ M6.CSS.logical BX CX, d ≤ M6.Pinned.weight v)
      (hz : ∀ v ∈ M6.CSS.logical BZ CZ, d ≤ M6.Pinned.weight v) :
      ∀ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, d ≤ M6.CSS.weight p := by
    intro p hp
    rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).mp hp).2.2 with hpX | hpZ
    · exact (hx p.1 hpX).trans (M6.CSS.support_bounds m p).1
    · exact (hz p.2 hpZ).trans (M6.CSS.support_bounds m p).2
  have sx := M6.Pinned.distance_spec m (M6.CSS.logical BX CX)
  have sz := M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)
  have sq := M6.CSS.quantum_distance_spec m BX CX BZ CZ
  cases hx : M6.Pinned.distance (M6.CSS.logical BX CX) with
  | none =>
    have ex := sx.1.mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have ez := sz.1.mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = none
      apply sq.1.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).mp hp).2.2 with hpX | hpZ
      · simpa [ex] using hpX
      · simpa [ez] using hpZ
    | some dz =>
      change M6.CSS.quantumDistance BX CX BZ CZ = some dz
      obtain ⟨⟨v, hv, hw⟩, hb⟩ := (sz.2 dz).mp hz
      apply (sq.2 dz).mpr
      refine ⟨⟨(0, v), pureZ v hv, (M6.CSS.pure_weights m v).2.trans hw⟩, ?_⟩
      apply lower dz
      · intro u hu
        simpa [ex] using hu
      · exact hb
  | some dx =>
    obtain ⟨⟨v, hv, hw⟩, hbX⟩ := (sx.2 dx).mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have ez := sz.1.mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = some dx
      apply (sq.2 dx).mpr
      refine ⟨⟨(v, 0), pureX v hv, (M6.CSS.pure_weights m v).1.trans hw⟩, ?_⟩
      apply lower dx hbX
      intro u hu
      simpa [ez] using hu
    | some dz =>
      obtain ⟨⟨w, hwz, hww⟩, hbZ⟩ := (sz.2 dz).mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = some (min dx dz)
      apply (sq.2 (min dx dz)).mpr
      constructor
      · by_cases h : dx ≤ dz
        · refine ⟨(v, 0), pureX v hv, ?_⟩
          simpa only [min_eq_left h] using (M6.CSS.pure_weights m v).1.trans hw
        · refine ⟨(0, w), pureZ w hwz, ?_⟩
          simpa only [min_eq_right (le_of_not_ge h)] using (M6.CSS.pure_weights m w).2.trans hww
      · apply lower (min dx dz)
        · intro u hu
          exact (min_le_left dx dz).trans (hbX u hu)
        · intro u hu
          exact (min_le_right dx dz).trans (hbZ u hu)

theorem M6.CSS.common_quantum_distance : ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ M6.CSS.logical BX CX ↔ J v ∈ M6.CSS.logical BZ CZ) → M6.CSS.quantumDistance BX CX BZ CZ = M6.Pinned.distance (M6.CSS.logical BX CX) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ M6.CSS.logical BX CX ↔ J v ∈ M6.CSS.logical BZ CZ) → M6.CSS.quantumDistance BX CX BZ CZ = M6.Pinned.distance (M6.CSS.logical BX CX)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ J hBX hBZ hBCX hBCZ hJ hw hmem
  have hd := M6.CSS.involution_distance m (M6.CSS.logical BX CX)
    (M6.CSS.logical BZ CZ) J hJ hw hmem
  rw [M6.CSS.css_distance_min m BX CX BZ CZ hBX hBZ hBCX hBCZ, ← hd]
  cases M6.Pinned.distance (M6.CSS.logical BX CX) <;>
    simp [M6.CSS.minDistance]

theorem M6.ActualCSS.J_boundary_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.Spaces.boundaryWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.subspaceWords (M6.Spaces.D N a b) := by
  intro N inst a b v
  classical
  have hJ (h : M6.Physical.Block N) :
      M6.Spaces.dualBoundary N a b h =
        M6.Flatten.J N (M6.Flatten.flatten N (M6.Physical.boundary N a b h)) := by
    rw [M6.Spaces.dual_boundary_eval]
    simp only [M6.Flatten.J, M6.Flatten.flatten_left]
  have hmem :
      M6.Flatten.J N v ∈ M6.Character.subspaceWords (M6.Spaces.D N a b) ↔
        ∃ h : M6.Physical.Block N,
          M6.Spaces.dualBoundary N a b h = M6.Flatten.J N v := by
    simp [M6.Character.subspaceWords, M6.Spaces.D, LinearMap.mem_range]
  rw [M6.Spaces.boundary_words_iff, hmem]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, (hJ h).trans (congrArg (M6.Flatten.J N) hh)⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hJ h] at hh
    have he := congrArg (M6.Flatten.J N) hh
    simpa only [M6.Flatten.J_involution] using he

theorem M6.ActualCSS.J_dot : ∀ (N : ℕ) [NeZero N] (v w : M6.Pinned.Vector (2*N)), M6.Character.dot (M6.Flatten.J N v) (M6.Flatten.J N w) = M6.Character.dot v w := by
  change ∀ (N : ℕ) [NeZero N] (v w : M6.Pinned.Vector (2*N)), M6.Character.dot (M6.Flatten.J N v) (M6.Flatten.J N w) = M6.Character.dot v w
  intro N _ v w
  have hrev (a b : M6.Physical.Block N) :
      M6.Physical.dot N (fun i => a (-i)) (fun i => b (-i)) =
        M6.Physical.dot N a b := by
    change (∑ i : ZMod N, a (-i) * b (-i)) = ∑ i : ZMod N, a i * b i
    exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun _ => rfl)
  have hJ (z t : M6.Physical.Word N) :
      M6.Physical.pairing N (M6.Physical.J N z) (M6.Physical.J N t) =
        M6.Physical.pairing N z t := by
    change M6.Physical.dot N (fun i => z.2 (-i)) (fun i => t.2 (-i)) +
        M6.Physical.dot N (fun i => z.1 (-i)) (fun i => t.1 (-i)) =
      M6.Physical.dot N z.1 t.1 + M6.Physical.dot N z.2 t.2
    rw [hrev, hrev, add_comm]
  unfold M6.Flatten.J
  rw [M6.Flatten.flatten_dot, hJ]
  exact (by simpa only [M6.Flatten.flatten_right] using
    (M6.Flatten.flatten_dot N (M6.Flatten.unflatten N v)
      (M6.Flatten.unflatten N w)).symm)

theorem M6.ActualCSS.zero_boundaries : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (0 : M6.Pinned.Vector (2*N)) ∈ M6.Spaces.boundaryWords N a b ∧ (0 : M6.Pinned.Vector (2*N)) ∈ M6.Character.subspaceWords (M6.Spaces.D N a b) := by
  intro N _ a b
  classical
  constructor <;> simp [M6.Spaces.boundaryWords, M6.Character.subspaceWords]

theorem M6.ActualCSS.J_cycle_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b) := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b)
  intro N inst a b v
  classical
  have hmem :
      M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b) ↔
        ∀ h : M6.Physical.Block N,
          M6.Character.dot (M6.Spaces.boundary N a b h) (M6.Flatten.J N v) = 0 := by
    unfold M6.Character.dualWords
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, M6.Character.Orthogonal, M6.Spaces.B, LinearMap.mem_range]
    constructor
    · intro hh h
      exact hh _ ⟨h, rfl⟩
    · intro hh q hq
      rcases hq with ⟨h, rfl⟩
      exact hh h
  have hpair (h : M6.Physical.Block N) :
      M6.Character.dot (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))) v =
        M6.Character.dot (M6.Spaces.boundary N a b h) (M6.Flatten.J N v) := by
    have hJ :
        M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)) =
          M6.Flatten.J N (M6.Spaces.boundary N a b h) := by
      rw [M6.Spaces.boundary_eval]
      simp only [M6.Flatten.J, M6.Flatten.flatten_left]
    rw [hJ]
    simpa only [M6.Flatten.J_involution] using
      (M6.ActualCSS.J_dot N (M6.Spaces.boundary N a b h) (M6.Flatten.J N v))
  rw [M6.Spaces.cycle_words_iff, M6.Flatten.cycle_orthogonal, hmem]
  simp only [hpair]

theorem M6.ActualCSS.J_logical_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.CSS.logical (M6.Spaces.boundaryWords N a b) (M6.Spaces.cycleWords N a b) ↔ M6.Flatten.J N v ∈ M6.CSS.logical (M6.Character.subspaceWords (M6.Spaces.D N a b)) (M6.Character.dualWords (M6.Spaces.B N a b)) := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.CSS.logical (M6.Spaces.boundaryWords N a b) (M6.Spaces.cycleWords N a b) ↔ M6.Flatten.J N v ∈ M6.CSS.logical (M6.Character.subspaceWords (M6.Spaces.D N a b)) (M6.Character.dualWords (M6.Spaces.B N a b))
  intro N inst a b v
  classical
  simp only [M6.CSS.logical, Finset.mem_sdiff, M6.ActualCSS.J_cycle_iff N a b v, M6.ActualCSS.J_boundary_iff N a b v]

theorem M6.ActualCSS.Z_boundaries_are_cycles : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Character.subspaceWords (M6.Spaces.D N a b) ⊆ M6.Character.dualWords (M6.Spaces.B N a b) := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Character.subspaceWords (M6.Spaces.D N a b) ⊆ M6.Character.dualWords (M6.Spaces.B N a b)
  intro N inst a b v hv
  have hb : M6.Flatten.J N v ∈ M6.Spaces.boundaryWords N a b := by
    apply (M6.ActualCSS.J_boundary_iff N a b (M6.Flatten.J N v)).mpr
    simpa only [M6.Flatten.J_involution] using hv
  have hc : M6.Flatten.J N v ∈ M6.Spaces.cycleWords N a b :=
    M6.Spaces.boundaries_are_cycles N a b hb
  simpa only [M6.Flatten.J_involution] using
    (M6.ActualCSS.J_cycle_iff N a b (M6.Flatten.J N v)).mp hc

theorem M6.ActualCSS.common_quantum_distance : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.CSS.quantumDistance (M6.Spaces.boundaryWords N a b) (M6.Spaces.cycleWords N a b) (M6.Character.subspaceWords (M6.Spaces.D N a b)) (M6.Character.dualWords (M6.Spaces.B N a b)) = M6.Pinned.distance (M6.Spaces.logicalWords N a b) := by
  intro N inst a b
  classical
  simpa only [M6.CSS.logical, M6.Spaces.logicalWords] using
    (M6.CSS.common_quantum_distance (2 * N)
      (M6.Spaces.boundaryWords N a b)
      (M6.Spaces.cycleWords N a b)
      (M6.Character.subspaceWords (M6.Spaces.D N a b))
      (M6.Character.dualWords (M6.Spaces.B N a b))
      (M6.Flatten.J N)
      (M6.ActualCSS.zero_boundaries N a b).1
      (M6.ActualCSS.zero_boundaries N a b).2
      (M6.Spaces.boundaries_are_cycles N a b)
      (M6.ActualCSS.Z_boundaries_are_cycles N a b)
      (M6.Flatten.J_involution N)
      (M6.Flatten.J_weight N)
      (M6.ActualCSS.J_logical_iff N a b))

theorem M6.Transfer.memory_follows : ∀ (R N : ℕ) [NeZero N] (h : M6.Transfer.Input N), M6.Transfer.Follows R N (M6.Transfer.memoryAt h) h := by
  change ∀ (R N : ℕ) [NeZero N] (h : M6.Transfer.Input N), M6.Transfer.Follows R N (M6.Transfer.memoryAt h) h
  intro R N inst h
  unfold M6.Transfer.Follows
  intro i
  funext j
  by_cases hj : j.val = 0
  · simp [M6.Transfer.memoryAt, M6.Transfer.shift, hj]
  · simp only [M6.Transfer.memoryAt, M6.Transfer.shift, dif_neg hj]
    apply congrArg h
    have hp : j.val - 1 + 1 = j.val := by omega
    rw [hp, Nat.cast_add, Nat.cast_one]
    ring

theorem M6.Transfer.output_convolution : ∀ (R N : ℕ) (c : Fin (R+1) → M6.Transfer.Bit) (h : M6.Transfer.Input N) (i : ZMod N), M6.Transfer.output c (M6.Transfer.memoryAt h i) (h i) = M6.Transfer.cyclicOutput c h i := by
  intro R N c h i
  simp [M6.Transfer.output, M6.Transfer.cyclicOutput, M6.Transfer.memoryAt, Fin.sum_univ_succ]

theorem M6.Transfer.shift_coordinates : ∀ (R : ℕ) (m : M6.Transfer.Memory (R+1)) (t : M6.Transfer.Bit), M6.Transfer.shift m t 0 = t ∧ ∀ j : Fin R, M6.Transfer.shift m t j.succ = m j.castSucc := by
  intro R m t
  constructor
  · rfl
  · intro j
    unfold M6.Transfer.shift
    split
    · rename_i h
      change j.val + 1 = 0 at h
      omega
    · apply congrArg m
      apply Fin.ext
      simp

theorem M6.Transfer.memory_forced : ∀ (R N : ℕ) [NeZero N] (p : M6.Transfer.ClosedWalk R N) (i : ZMod N) (j : Fin R), p.val.1 i j = M6.Transfer.labels p (i - (j.val + 1 : ℕ)) := by
  intro R N inst p
  have aux : ∀ (n : ℕ) (hn : n < R) (i : ZMod N),
      p.val.1 i ⟨n, hn⟩ = M6.Transfer.labels p (i - (n + 1 : ℕ)) := by
    intro n
    induction n with
    | zero =>
        intro hn i
        have h := congrFun (p.property (i - 1)) (⟨0, hn⟩ : Fin R)
        simpa [M6.Transfer.shift, M6.Transfer.labels] using h
    | succ n ih =>
        intro hn i
        have h := congrFun (p.property (i - 1)) (⟨n + 1, hn⟩ : Fin R)
        have hs : p.val.1 i ⟨n + 1, hn⟩ =
            p.val.1 (i - 1) ⟨n, by omega⟩ := by
          simpa [M6.Transfer.shift] using h
        rw [hs, ih (by omega) (i - 1)]
        congr 1
        push_cast <;> ring
  intro i j
  exact aux j.val j.isLt i

theorem M6.Transfer.labels_bijective : ∀ (R N : ℕ) [NeZero N], Function.Bijective (M6.Transfer.labels : M6.Transfer.ClosedWalk R N → M6.Transfer.Input N) := by
  change ∀ (R N : ℕ) [NeZero N], Function.Bijective (M6.Transfer.labels : M6.Transfer.ClosedWalk R N → M6.Transfer.Input N)
  intro R N inst
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · funext i j
      rw [M6.Transfer.memory_forced R N p i j,
        M6.Transfer.memory_forced R N q i j, hpq]
    · exact hpq
  · intro h
    exact ⟨⟨(M6.Transfer.memoryAt h, h), M6.Transfer.memory_follows R N h⟩, rfl⟩

theorem M6.Transfer.closed_walk_card : ∀ (R N : ℕ) [NeZero N], Fintype.card (M6.Transfer.ClosedWalk R N) = 2 ^ N := by
  change ∀ (R N : ℕ) [NeZero N], Fintype.card (M6.Transfer.ClosedWalk R N) = 2 ^ N
  intro R N inst
  classical
  calc
    Fintype.card (M6.Transfer.ClosedWalk R N) = Fintype.card (M6.Transfer.Input N) :=
      Fintype.card_congr (Equiv.ofBijective M6.Transfer.labels (M6.Transfer.labels_bijective R N))
    _ = 2 ^ N := by
      simp [M6.Transfer.Input, M6.Transfer.Bit, Fintype.card_fun, ZMod.card]

theorem M6.Transfer.indexed_weight_sum : ∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ZMod N → M6.Transfer.Memory R → M6.Transfer.Bit → K), (∑ p : M6.Transfer.ClosedWalk R N, ∏ i : ZMod N, W i (p.val.1 i) (M6.Transfer.labels p i)) = ∑ h : M6.Transfer.Input N, ∏ i : ZMod N, W i (M6.Transfer.memoryAt h i) (h i) := by
  intro R N instN K instK W
  classical
  have hm (p : M6.Transfer.ClosedWalk R N) (i : ZMod N) :
      p.val.1 i = M6.Transfer.memoryAt (M6.Transfer.labels p) i := by
    funext j
    exact M6.Transfer.memory_forced R N p i j
  simp_rw [hm]
  let e : M6.Transfer.ClosedWalk R N ≃ M6.Transfer.Input N :=
    Equiv.ofBijective M6.Transfer.labels (M6.Transfer.labels_bijective R N)
  exact e.sum_comp (fun h => ∏ i : ZMod N, W i (M6.Transfer.memoryAt h i) (h i))

theorem M6.Transfer.layers_matrix : ∀ (R : ℕ) (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K) (start finish : M6.Transfer.Memory R) (n : ℕ), M6.Transfer.layers W start n finish = M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) n start finish := by
  classical
  intro R K inst W start finish n
  induction n generalizing finish with
  | zero =>
      simp [M6.Transfer.layers, M6.Transfer.matrixProduct, Matrix.one_apply, eq_comm]
  | succ n ih =>
      simp only [M6.Transfer.layers, M6.Transfer.propagate,
        M6.Transfer.matrixProduct, Matrix.mul_apply, M6.Transfer.edgeMatrix,
        Finset.mul_sum, mul_ite, mul_zero, ih]

theorem M6.Transfer.matrix_trace_cycle : ∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (N : ℕ) [NeZero N] (A : ℕ → Matrix S S K), Matrix.trace (M6.Transfer.matrixProduct A N) = ∑ m : ZMod N → S, ∏ i : ZMod N, A i.val (m i) (m (i+1)) := by
  classical
  intro S K _ _ _ N _ A
  have sum_snoc (n : ℕ) (f : (Fin (n + 1) → S) → K) :
      (∑ m, f m) = ∑ m : Fin n → S, ∑ b : S, f (Fin.snoc m b) := by
    let e : ((Fin n → S) × S) ≃ (Fin (n + 1) → S) :=
      { toFun := fun p => Fin.snoc p.1 p.2
        invFun := fun m => (fun i => m i.castSucc, m (Fin.last n))
        left_inv := by intro p; simp
        right_inv := by
          intro m
          funext i
          cases i using Fin.lastCases <;> simp }
    calc
      (∑ m, f m) = ∑ p, f (e p) := (e.sum_comp f).symm
      _ = ∑ m : Fin n → S, ∑ b : S, f (Fin.snoc m b) := by
        change (∑ p : (Fin n → S) × S, f (Fin.snoc p.1 p.2)) = _
        exact Fintype.sum_prod_type (fun p : (Fin n → S) × S => f (Fin.snoc p.1 p.2))
  have expansion : ∀ n (B : Matrix S S K),
      Matrix.trace (M6.Transfer.matrixProduct A n * B) =
        ∑ m : Fin (n + 1) → S,
          (∏ i : Fin n, A i.val (m i.castSucc) (m i.succ)) *
            B (m (Fin.last n)) (m 0) := by
    intro n
    induction n with
    | zero =>
        intro B
        simpa [M6.Transfer.matrixProduct, Matrix.trace, Fin.snoc] using
          (sum_snoc 0 (fun m => B (m (Fin.last 0)) (m 0))).symm
    | succ n ih =>
        intro B
        rw [M6.Transfer.matrixProduct, Matrix.mul_assoc, ih]
        simp only [Matrix.mul_apply, Finset.mul_sum]
        conv_rhs => rw [sum_snoc (n + 1)]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro b _
        have hs (i : Fin n) :
            (Fin.snoc m b : Fin (n+2) → S) i.castSucc.succ = m i.succ := by
          exact Fin.snoc_castSucc (α := fun _ : Fin (n+2) => S) b m i.succ
        have hz : (Fin.snoc m b : Fin (n+2) → S) 0 = m 0 := by
          change (Fin.snoc m b : Fin (n+2) → S) (Fin.castSucc (0 : Fin (n + 1))) = m 0
          simp
        simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, Fin.val_castSucc, Fin.val_last, hs, hz, mul_assoc]
        congr 2
        congr 1
        exact (Fin.snoc_last (α := fun _ : Fin (n+2) => S) b m).symm
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [M6.Transfer.matrixProduct, expansion]
      change (∑ m : Fin (n + 1) → S,
        (∏ i : Fin n, A i.val (m i.castSucc) (m i.succ)) *
          A n (m (Fin.last n)) (m 0)) =
        ∑ m : Fin (n + 1) → S,
          ∏ i : Fin (n + 1), A i.val (m i) (m (i + 1))
      apply Finset.sum_congr rfl
      intro m _
      have hs (i : Fin n) : i.castSucc + 1 = i.succ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one', Fin.val_castSucc, Fin.val_succ, Nat.add_mod_mod]
        exact Nat.mod_eq_of_lt i.succ.isLt
      have hl : (Fin.last n : Fin (n + 1)) + 1 = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one', Fin.val_last, Fin.val_zero, Nat.add_mod_mod]
        exact Nat.mod_self _
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hs, hl]

theorem M6.Transfer.uniform_matrix_power : ∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (A : Matrix S S K) (N : ℕ), M6.Transfer.matrixProduct (fun _ => A) N = A ^ N := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (A : Matrix S S K) (N : ℕ), M6.Transfer.matrixProduct (fun _ => A) N = A ^ N
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro S K _ _ _ A N
  induction N with
  | zero => rfl
  | succ n ih =>
      simpa only [M6.Transfer.matrixProduct, pow_succ] using congrArg (fun B : Matrix S S K => B * A) ih

theorem M6.Transfer.array_trace_matrix : ∀ (R : ℕ) (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K) (N : ℕ), M6.Transfer.arrayTrace W N = Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N) := by
  classical
  intro R K inst W N
  change (∑ start : M6.Transfer.Memory R, M6.Transfer.layers W start N start) =
    ∑ start : M6.Transfer.Memory R, M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N start start
  apply Finset.sum_congr rfl
  intro start hstart
  exact M6.Transfer.layers_matrix R K W start start N

theorem M6.Transfer.labelled_trace : ∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K), Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N) = ∑ p : M6.Transfer.ClosedWalk R N, ∏ i : ZMod N, W i.val (p.val.1 i) (M6.Transfer.labels p i) := by
  classical
  intro R N _ K _ W
  have hprod (m : ZMod N → M6.Transfer.Memory R) (h : M6.Transfer.Input N) :
      (∏ i : ZMod N, if M6.Transfer.shift (m i) (h i) = m (i + 1)
        then W i.val (m i) (h i) else 0) =
      if M6.Transfer.Follows R N m h then ∏ i : ZMod N, W i.val (m i) (h i) else 0 := by
    by_cases hf : M6.Transfer.Follows R N m h
    · rw [if_pos hf]
      apply Finset.prod_congr rfl
      intro i _
      exact if_pos (hf i).symm
    · rw [if_neg hf]
      unfold M6.Transfer.Follows at hf
      push_neg at hf
      obtain ⟨i, hi⟩ := hf
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_neg (Ne.symm hi)
  let T := (ZMod N → M6.Transfer.Memory R) × M6.Transfer.Input N
  let P : T → Prop := fun q => M6.Transfer.Follows R N q.1 q.2
  let f : T → K := fun q => ∏ i : ZMod N, W i.val (q.1 i) (q.2 i)
  rw [M6.Transfer.matrix_trace_cycle (M6.Transfer.Memory R) K N]
  simp only [M6.Transfer.edgeMatrix, Fintype.prod_sum]
  calc
    (∑ m : ZMod N → M6.Transfer.Memory R, ∑ h : M6.Transfer.Input N,
        ∏ i : ZMod N, if M6.Transfer.shift (m i) (h i) = m (i + 1)
          then W i.val (m i) (h i) else 0) =
        ∑ q : T, if P q then f q else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro h _
      exact hprod m h
    _ = ∑ q ∈ Finset.univ.filter P, f q := by
      rw [Finset.sum_filter]
    _ = ∑ p : M6.Transfer.ClosedWalk R N,
        ∏ i : ZMod N, W i.val (p.val.1 i) (M6.Transfer.labels p i) := by
      apply Finset.sum_bij
        (fun q hq => (⟨q, (Finset.mem_filter.mp hq).2⟩ : M6.Transfer.ClosedWalk R N))
      · intro q hq
        exact Finset.mem_univ _
      · intro a ha b hb hab
        exact congrArg Subtype.val hab
      · intro p hp
        exact ⟨p.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.property⟩, rfl⟩
      · intro q hq
        rfl

theorem M6.Transfer.array_trace_inputs : ∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K), M6.Transfer.arrayTrace W N = ∑ h : M6.Transfer.Input N, ∏ i : ZMod N, W i.val (M6.Transfer.memoryAt h i) (h i) := by
  classical
  intro R N instN K instK W
  rw [M6.Transfer.array_trace_matrix R K W N,
    M6.Transfer.labelled_trace R N K W]
  exact M6.Transfer.indexed_weight_sum R N K (fun i => W i.val)

theorem M6.Transfer.layers_degree : ∀ (R : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start finish : M6.Transfer.Memory R) (n : ℕ), (∀ i m t, (W i m t).natDegree ≤ 2) → (M6.Transfer.layers W start n finish).natDegree ≤ 2*n := by
  classical
  intro R W start finish n hW
  induction n generalizing finish with
  | zero =>
      by_cases h : finish = start <;>
        simp [M6.Transfer.layers, h]
  | succ n ih =>
      simp only [M6.Transfer.layers, M6.Transfer.propagate]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro m hm
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro t ht
      split_ifs with h
      · have hmul := Polynomial.natDegree_mul_le (p := M6.Transfer.layers W start n m) (q := W n m t)
        exact (hmul.trans (Nat.add_le_add (ih m) (hW n m t))).trans_eq (by simp [Nat.mul_succ])
      · simp

theorem M6.Transfer.mass_add : ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p+q) ≤ M6.Transfer.polynomialMass p + M6.Transfer.polynomialMass q := by
  change ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p + q) ≤ M6.Transfer.polynomialMass p + M6.Transfer.polynomialMass q
  intro p q
  classical
  unfold M6.Transfer.polynomialMass
  have hp : p.support ⊆ p.support ∪ q.support := Finset.subset_union_left
  have hq : q.support ⊆ p.support ∪ q.support := Finset.subset_union_right
  have hpq : (p + q).support ⊆ p.support ∪ q.support := Polynomial.support_add
  rw [Polynomial.sum_eq_of_subset (p := p + q) (fun (_ : ℕ) (c : ℤ) => c.natAbs) (by intro i; rfl) hpq,
      Polynomial.sum_eq_of_subset (p := p) (fun (_ : ℕ) (c : ℤ) => c.natAbs) (by intro i; rfl) hp,
      Polynomial.sum_eq_of_subset (p := q) (fun (_ : ℕ) (c : ℤ) => c.natAbs) (by intro i; rfl) hq,
      ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [Polynomial.coeff_add] using Int.natAbs_add_le (p.coeff i) (q.coeff i)

theorem M6.Transfer.mass_basic : M6.Transfer.polynomialMass (0 : Polynomial ℤ) = 0 ∧ M6.Transfer.polynomialMass (1 : Polynomial ℤ) = 1 ∧ (∀ (n : ℕ) (c : ℤ), M6.Transfer.polynomialMass (Polynomial.monomial n c) = c.natAbs) ∧ ∀ (p : Polynomial ℤ) (d : ℕ), (p.coeff d).natAbs ≤ M6.Transfer.polynomialMass p := by
  let QuantumHarnessFrozenTarget : Prop := (
    M6.Transfer.polynomialMass (0 : Polynomial ℤ) = 0 ∧ M6.Transfer.polynomialMass (1 : Polynomial ℤ) = 1 ∧ (∀ (n : ℕ) (c : ℤ), M6.Transfer.polynomialMass (Polynomial.monomial n c) = c.natAbs) ∧ ∀ (p : Polynomial ℤ) (d : ℕ), (p.coeff d).natAbs ≤ M6.Transfer.polynomialMass p
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  have hm : ∀ (n : ℕ) (c : ℤ), M6.Transfer.polynomialMass (Polynomial.monomial n c) = c.natAbs := by
    intro n c
    simp [M6.Transfer.polynomialMass, Polynomial.sum_monomial_index]
  refine ⟨?_, ?_, hm, ?_⟩
  · simp [M6.Transfer.polynomialMass]
  · simpa using hm 0 1
  · intro p d
    by_cases h : p.coeff d = 0
    · simp [h]
    · change (p.coeff d).natAbs ≤ ∑ n ∈ p.support, (p.coeff n).natAbs
      exact Finset.single_le_sum
        (f := fun n => (p.coeff n).natAbs)
        (fun n _ => Nat.zero_le ((p.coeff n).natAbs))
        (Polynomial.mem_support_iff.mpr h)

theorem M6.Transfer.mass_sum : ∀ (I : Type) (s : Finset I) (f : I → Polynomial ℤ), M6.Transfer.polynomialMass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, M6.Transfer.polynomialMass (f i) := by
  change ∀ (I : Type) (s : Finset I) (f : I → Polynomial ℤ), M6.Transfer.polynomialMass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, M6.Transfer.polynomialMass (f i)
  intro I s f
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, M6.Transfer.mass_basic.1, le_refl]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (M6.Transfer.mass_add (f a) (∑ i ∈ s, f i)).trans
        (Nat.add_le_add_left ih (M6.Transfer.polynomialMass (f a)))

theorem M6.Transfer.mass_mul : ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p*q) ≤ M6.Transfer.polynomialMass p * M6.Transfer.polynomialMass q := by
  change ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p * q) ≤ M6.Transfer.polynomialMass p * M6.Transfer.polynomialMass q
  intro p q
  classical
  rw [Polynomial.mul_eq_sum_sum]
  refine (M6.Transfer.mass_sum ℕ p.support _).trans ?_
  calc
    _ ≤ ∑ i ∈ p.support, (p.coeff i).natAbs * M6.Transfer.polynomialMass q := by
      apply Finset.sum_le_sum
      intro i hi
      change M6.Transfer.polynomialMass (∑ j ∈ q.support, Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) ≤ (p.coeff i).natAbs * M6.Transfer.polynomialMass q
      refine (M6.Transfer.mass_sum ℕ q.support _).trans ?_
      simp only [M6.Transfer.mass_basic.2.2.1, Int.natAbs_mul]
      change (∑ j ∈ q.support, (p.coeff i).natAbs * (q.coeff j).natAbs) ≤ (p.coeff i).natAbs * (∑ j ∈ q.support, (q.coeff j).natAbs)
      rw [Finset.mul_sum]
    _ = M6.Transfer.polynomialMass p * M6.Transfer.polynomialMass q := by
      change (∑ i ∈ p.support, (p.coeff i).natAbs * M6.Transfer.polynomialMass q) = (∑ i ∈ p.support, (p.coeff i).natAbs) * M6.Transfer.polynomialMass q
      rw [Finset.sum_mul]

theorem M6.Transfer.propagate_mass : ∀ (R : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (v : M6.Transfer.Memory R → Polynomial ℤ), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.propagate W v) ≤ 8 * M6.Transfer.rowMass v := by
  change ∀ (R : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (v : M6.Transfer.Memory R → Polynomial ℤ), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.propagate W v) ≤ 8 * M6.Transfer.rowMass v
  intro R W v hW
  classical
  have hc : Fintype.card M6.Transfer.Bit = 2 := by
    simp [M6.Transfer.Bit]
  calc
    M6.Transfer.rowMass (M6.Transfer.propagate W v)
        ≤ ∑ n : M6.Transfer.Memory R, ∑ m : M6.Transfer.Memory R,
            ∑ t : M6.Transfer.Bit, M6.Transfer.polynomialMass
              (if M6.Transfer.shift m t = n then v m * W m t else 0) := by
      unfold M6.Transfer.rowMass M6.Transfer.propagate
      apply Finset.sum_le_sum
      intro n hn
      refine (M6.Transfer.mass_sum _ Finset.univ _).trans ?_
      apply Finset.sum_le_sum
      intro m hm
      exact M6.Transfer.mass_sum _ Finset.univ _
    _ = ∑ m : M6.Transfer.Memory R, ∑ t : M6.Transfer.Bit,
          M6.Transfer.polynomialMass (v m * W m t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [apply_ite, M6.Transfer.mass_basic.1]
      simp
    _ ≤ ∑ m : M6.Transfer.Memory R, ∑ t : M6.Transfer.Bit,
          M6.Transfer.polynomialMass (v m) * 4 := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro t ht
      exact (M6.Transfer.mass_mul (v m) (W m t)).trans
        (Nat.mul_le_mul_left _ (hW m t))
    _ = ∑ m : M6.Transfer.Memory R, 8 * M6.Transfer.polynomialMass (v m) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      ring
    _ = 8 * M6.Transfer.rowMass v := by
      unfold M6.Transfer.rowMass
      rw [Finset.mul_sum]

theorem M6.Transfer.layers_mass : ∀ (R : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start : M6.Transfer.Memory R) (n : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.layers W start n) ≤ 8^n := by
  change ∀ (R : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start : M6.Transfer.Memory R) (n : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.layers W start n) ≤ 8 ^ n
  intro R W start n hW
  classical
  induction n with
  | zero =>
      simp [M6.Transfer.layers, M6.Transfer.rowMass, apply_ite,
        M6.Transfer.mass_basic.1, M6.Transfer.mass_basic.2.1]
  | succ n ih =>
      change M6.Transfer.rowMass (M6.Transfer.propagate (W n) (M6.Transfer.layers W start n)) ≤ 8 ^ (n + 1)
      calc
        _ ≤ 8 * M6.Transfer.rowMass (M6.Transfer.layers W start n) :=
          M6.Transfer.propagate_mass R (W n) (M6.Transfer.layers W start n) (hW n)
        _ ≤ 8 * 8 ^ n := Nat.mul_le_mul_left 8 ih
        _ = 8 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

theorem M6.Transfer.trace_coefficient_bound : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → ((M6.Transfer.arrayTrace W N).coeff d).natAbs ≤ 2^R * 8^N := by
  change ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → ((M6.Transfer.arrayTrace W N).coeff d).natAbs ≤ 2 ^ R * 8 ^ N
  intro R N W d hW
  classical
  have hc : Fintype.card (M6.Transfer.Memory R) = 2 ^ R := by
    simp [M6.Transfer.Memory, M6.Transfer.Bit]
  calc
    ((M6.Transfer.arrayTrace W N).coeff d).natAbs
        ≤ M6.Transfer.polynomialMass (M6.Transfer.arrayTrace W N) :=
      M6.Transfer.mass_basic.2.2.2 _ d
    _ ≤ ∑ start : M6.Transfer.Memory R,
          M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) := by
      unfold M6.Transfer.arrayTrace
      exact M6.Transfer.mass_sum _ Finset.univ _
    _ ≤ ∑ _start : M6.Transfer.Memory R, (8 ^ N : ℕ) := by
      apply Finset.sum_le_sum
      intro start hstart
      have hd : M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) ≤
          M6.Transfer.rowMass (M6.Transfer.layers W start N) := by
        unfold M6.Transfer.rowMass
        exact Finset.single_le_sum
          (fun m _ => Nat.zero_le (M6.Transfer.polynomialMass (M6.Transfer.layers W start N m)))
          (Finset.mem_univ start)
      exact hd.trans (M6.Transfer.layers_mass R W start N hW)
    _ = 2 ^ R * 8 ^ N := by
      simp [hc, nsmul_eq_mul]

theorem M6.Transfer.scatter_event_count : ∀ R N : ℕ, Fintype.card (M6.Transfer.Memory R) * N * (M6.Transfer.scatterEventList R N).length = M6.Transfer.traceCoefficientOps R N := by
  change ∀ R N : ℕ, Fintype.card (M6.Transfer.Memory R) * N * (M6.Transfer.scatterEventList R N).length = M6.Transfer.traceCoefficientOps R N
  intro R N
  classical
  simp [M6.Transfer.scatterEventList, M6.Transfer.traceCoefficientOps, Finset.length_toList, Finset.card_univ]

theorem M6.Transfer.scatter_prefix_formula : ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input initial : M6.Transfer.CoefficientArray R N) (l : List (M6.Transfer.ScatterEvent R N)) (addr : M6.Transfer.CoefficientAddress R N), (l.foldl (M6.Transfer.scatterUpdate W input) initial) addr = initial addr + (l.map (fun e => if M6.Transfer.eventDestination e = some addr then M6.Transfer.eventTerm W input e else 0)).sum := by
  classical
  intro R N W input initial l addr
  induction l generalizing initial with
  | nil => simp
  | cons e l ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      cases h : M6.Transfer.eventDestination e with
      | none =>
          simp [M6.Transfer.scatterUpdate, h]
      | some a =>
          by_cases ha : a = addr
          · subst a
            simp [M6.Transfer.scatterUpdate, h, add_assoc]
          · simp [M6.Transfer.scatterUpdate, h, Function.update_apply, ha, Ne.symm ha]

theorem M6.Transfer.small_polynomial_convolution : ∀ (p q : Polynomial ℤ) (d : ℕ), q.natDegree ≤ 2 → (p*q).coeff d = ∑ e : Fin 3, if e.val ≤ d then p.coeff (d-e.val) * q.coeff e.val else 0 := by
  change ∀ (p q : Polynomial ℤ) (d : ℕ), q.natDegree ≤ 2 → _
  intro p q d hqdeg
  have hq : q = Polynomial.monomial 0 (q.coeff 0) +
      Polynomial.monomial 1 (q.coeff 1) +
      Polynomial.monomial 2 (q.coeff 2) := by
    ext n
    by_cases hn : n ≤ 2
    · interval_cases n <;>
        simp only [Polynomial.coeff_add, Polynomial.coeff_monomial] <;> norm_num
    · have hz : q.coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h0 : 0 ≠ n := by omega
      have h1 : 1 ≠ n := by omega
      have h2 : 2 ≠ n := by omega
      simp only [Polynomial.coeff_add, Polynomial.coeff_monomial,
        if_neg h0, if_neg h1, if_neg h2, hz, add_zero]
  have hm : ∀ (n : ℕ) (r : ℤ),
      (p * Polynomial.monomial n r).coeff d =
        if n ≤ d then p.coeff (d - n) * r else 0 := by
    intro n r
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc,
      Polynomial.coeff_mul_X_pow']
    split_ifs <;> simp [Polynomial.coeff_mul_C]
  conv_lhs => rw [hq]
  simp only [mul_add, Polynomial.coeff_add, hm]
  have h1 : (1 ≤ d) ↔ (0 < d) := by omega
  have h2 : (2 ≤ d) ↔ (1 < d) := by omega
  simp [Fin.sum_univ_succ, h1, h2, add_assoc]

theorem M6.Transfer.scatter_polynomial_coeff : ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (v : M6.Transfer.Memory R → Polynomial ℤ) (addr : M6.Transfer.CoefficientAddress R N), (∀ m t, (W m t).natDegree ≤ 2) → M6.Transfer.scatterLayer W (M6.Transfer.encodeCoefficients v) addr = (M6.Transfer.propagate W v addr.1).coeff addr.2.val := by
  classical
  intro R N W v addr hW
  rcases addr with ⟨n, d⟩
  have hd (m : M6.Transfer.Memory R) (t : M6.Transfer.Bit)
      (i : Fin (2 * N + 1)) (e : Fin 3) :
      M6.Transfer.eventDestination (m, t, i, e) = some (n, d) ↔
        M6.Transfer.shift m t = n ∧ i.val + e.val = d.val := by
    by_cases h : i.val + e.val < 2 * N + 1
    · simp [M6.Transfer.eventDestination, h, Prod.mk.injEq, Fin.ext_iff]
    · have hne : i.val + e.val ≠ d.val := by omega
      simp [M6.Transfer.eventDestination, h, hne]
  unfold M6.Transfer.scatterLayer
  rw [M6.Transfer.scatter_prefix_formula]
  simp only [zero_add, M6.Transfer.scatterEventList, Finset.sum_map_toList]
  change (∑ x : M6.Transfer.Memory R × (M6.Transfer.Bit × (Fin (2 * N + 1) × Fin 3)),
      if M6.Transfer.eventDestination x = some (n, d) then
        M6.Transfer.eventTerm W (M6.Transfer.encodeCoefficients v) x else 0) = _
  simp only [Fintype.sum_prod_type, hd, M6.Transfer.eventTerm,
    M6.Transfer.encodeCoefficients, M6.Transfer.propagate,
    Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : M6.Transfer.shift m t = n
  · simp only [hs, true_and, if_true]
    rw [M6.Transfer.small_polynomial_convolution (v m) (W m t) d.val (hW m t)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hle : e.val ≤ d.val
    · simp only [if_pos hle]
      let i₀ : Fin (2 * N + 1) := ⟨d.val - e.val, by omega⟩
      rw [Finset.sum_eq_single i₀]
      · have hi : i₀.val + e.val = d.val := by
          dsimp [i₀]
          omega
        simp [hi, i₀]
      · intro i hi hne
        have hsum : i.val + e.val ≠ d.val := by
          intro heq
          apply hne
          apply Fin.ext
          dsimp [i₀]
          omega
        simp [hsum]
      · simp
    · have hsum (i : Fin (2 * N + 1)) : i.val + e.val ≠ d.val := by omega
      simp [hle, hsum]
  · simp [hs]

theorem M6.Transfer.scalar_layers_exact : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start : M6.Transfer.Memory R) (k : ℕ), (∀ i m t, (W i m t).natDegree ≤ 2) → M6.Transfer.scalarLayers (N:=N) W start k = M6.Transfer.encodeCoefficients (M6.Transfer.layers W start k) := by
  classical
  intro R N W start k hW
  induction k with
  | zero =>
      funext addr
      change (if addr.1 = start ∧ addr.2.val = 0 then (1 : ℤ) else 0) =
        (if addr.1 = start then (1 : Polynomial ℤ) else 0).coeff addr.2.val
      by_cases hm : addr.1 = start
      · rw [if_pos hm]
        change (if addr.1 = start ∧ addr.2.val = 0 then (1 : ℤ) else 0) =
          (Polynomial.C (1 : ℤ)).coeff addr.2.val
        rw [Polynomial.coeff_C]
        simp [hm, eq_comm]
      · simp [hm]
  | succ k ih =>
      change M6.Transfer.scatterLayer (W k) (M6.Transfer.scalarLayers W start k) =
        M6.Transfer.encodeCoefficients (M6.Transfer.propagate (W k) (M6.Transfer.layers W start k))
      rw [ih]
      funext addr
      exact M6.Transfer.scatter_polynomial_coeff R N (W k)
        (M6.Transfer.layers W start k) addr (hW k)

theorem M6.Transfer.scalar_trace_coefficient : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : Fin (2*N+1)), (∀ i m t, (W i m t).natDegree ≤ 2) → M6.Transfer.scalarTraceCoefficient W N d = (M6.Transfer.arrayTrace W N).coeff d.val := by
  classical
  intro R N W d hW
  unfold M6.Transfer.scalarTraceCoefficient M6.Transfer.arrayTrace
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro start hstart
  rw [M6.Transfer.scalar_layers_exact R N W start N hW]
  rfl

theorem M6.Transfer.scalar_trace_polynomial : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ), (∀ i m t, (W i m t).natDegree ≤ 2) → M6.Transfer.scalarTracePolynomial W N = M6.Transfer.arrayTrace W N := by
  classical
  intro R N W hW
  change M6.Transfer.scalarTracePolynomial W N = M6.Transfer.arrayTrace W N
  apply Polynomial.ext
  intro d
  rw [M6.Transfer.scalarTracePolynomial, Polynomial.finset_sum_coeff]
  by_cases hd : d < 2 * N + 1
  · let j : Fin (2 * N + 1) := ⟨d, hd⟩
    calc
      _ = (Polynomial.monomial j.val (M6.Transfer.scalarTraceCoefficient W N j)).coeff d := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          have hv : i.val ≠ d := by
            intro he
            apply hij
            apply Fin.ext
            exact he
          simp [Polynomial.coeff_monomial, hv, Ne.symm hv]
        · simp
      _ = M6.Transfer.scalarTraceCoefficient W N j := by
        simp [j]
      _ = (M6.Transfer.arrayTrace W N).coeff d :=
        M6.Transfer.scalar_trace_coefficient R N W j hW
  · have hleft : (∑ i : Fin (2 * N + 1),
        (Polynomial.monomial i.val (M6.Transfer.scalarTraceCoefficient W N i)).coeff d) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hv : i.val ≠ d := by
        have := i.isLt
        omega
      simp [Polynomial.coeff_monomial, hv, Ne.symm hv]
    rw [hleft]
    symm
    rw [M6.Transfer.arrayTrace, Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro start hstart
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hdeg := M6.Transfer.layers_degree R W start start N hW
    omega

theorem M6.Transfer.boundary_factor_bounds : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2), M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s) ≤ 1 ∧ (M6.Character.boundaryFactor P i s).natDegree ≤ 1 := by
  classical
  intro m P i s
  by_cases h : P i = none ∨ P i = some s
  · simp only [M6.Character.boundaryFactor, if_pos h]
    constructor
    · have hx : (Polynomial.X : Polynomial ℤ) ^ s.val = Polynomial.monomial s.val 1 := by
        ext n
        simp [Polynomial.coeff_monomial, eq_comm]
      rw [hx, M6.Transfer.mass_basic.2.2.1]
      norm_num
    · have hs := ZMod.val_lt s
      rw [Polynomial.natDegree_X_pow]
      omega
  · simp [M6.Character.boundaryFactor, h, M6.Transfer.mass_basic.1]

theorem M6.Transfer.boundary_edge_bounds : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i j : Fin m) (s t : ZMod 2), M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s * M6.Character.boundaryFactor P j t) ≤ 4 ∧ (M6.Character.boundaryFactor P i s * M6.Character.boundaryFactor P j t).natDegree ≤ 2 := by
  intro m P i j s t
  obtain ⟨hmi, hdi⟩ := M6.Transfer.boundary_factor_bounds m P i s
  obtain ⟨hmj, hdj⟩ := M6.Transfer.boundary_factor_bounds m P j t
  constructor
  · calc
      M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s * M6.Character.boundaryFactor P j t)
          ≤ M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s) *
            M6.Transfer.polynomialMass (M6.Character.boundaryFactor P j t) :=
        M6.Transfer.mass_mul _ _
      _ ≤ 1 * 1 := Nat.mul_le_mul hmi hmj
      _ ≤ 4 := by norm_num
  · exact le_trans Polynomial.natDegree_mul_le (by omega)

theorem M6.Transfer.character_factor_bounds : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2), M6.Transfer.polynomialMass (M6.Character.pinnedCharacterFactor P i s) ≤ 2 ∧ (M6.Character.pinnedCharacterFactor P i s).natDegree ≤ 1 := by
  classical
  intro m P i s
  let f : ZMod 2 → Polynomial ℤ := fun t =>
    Polynomial.C (M6.Character.sign (s * t)) * M6.Character.boundaryFactor P i t
  have hm (t : ZMod 2) : M6.Transfer.polynomialMass (f t) ≤ 1 := by
    have hc : M6.Transfer.polynomialMass (Polynomial.C (M6.Character.sign (s * t))) = 1 := by
      simpa [M6.Character.sign] using
        (M6.Transfer.mass_basic.2.2.1 0 (M6.Character.sign (s * t)))
    have h := M6.Transfer.mass_mul
      (Polynomial.C (M6.Character.sign (s * t))) (M6.Character.boundaryFactor P i t)
    change M6.Transfer.polynomialMass (f t) ≤ _ at h
    rw [hc, one_mul] at h
    exact le_trans h (M6.Transfer.boundary_factor_bounds m P i t).1
  have hd (t : ZMod 2) : (f t).natDegree ≤ 1 := by
    have h : (f t).natDegree ≤ (M6.Character.boundaryFactor P i t).natDegree := by
      simpa [f] using
        (Polynomial.natDegree_mul_le
          (p := Polynomial.C (M6.Character.sign (s * t)))
          (q := M6.Character.boundaryFactor P i t))
    exact le_trans h (M6.Transfer.boundary_factor_bounds m P i t).2
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have he : M6.Character.pinnedCharacterFactor P i s = f 0 + f 1 := by
    change (∑ t : ZMod 2, f t) = f 0 + f 1
    rw [hu]
    simp
  rw [he]
  constructor
  · exact le_trans (M6.Transfer.mass_add (f 0) (f 1)) (by have h0 := hm 0; have h1 := hm 1; omega)
  · exact le_trans (Polynomial.natDegree_add_le (f 0) (f 1)) (max_le (hd 0) (hd 1))

theorem M6.Transfer.character_edge_bounds : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i j : Fin m) (s t : ZMod 2), M6.Transfer.polynomialMass (M6.Character.pinnedCharacterFactor P i s * M6.Character.pinnedCharacterFactor P j t) ≤ 4 ∧ (M6.Character.pinnedCharacterFactor P i s * M6.Character.pinnedCharacterFactor P j t).natDegree ≤ 2 := by
  intro m P i j s t
  have hi := M6.Transfer.character_factor_bounds m P i s
  have hj := M6.Transfer.character_factor_bounds m P j t
  constructor
  · exact le_trans
      (M6.Transfer.mass_mul
        (M6.Character.pinnedCharacterFactor P i s)
        (M6.Character.pinnedCharacterFactor P j t))
      (by simpa using Nat.mul_le_mul hi.1 hj.1)
  · exact le_trans
      (Polynomial.natDegree_mul_le
        (p := M6.Character.pinnedCharacterFactor P i s)
        (q := M6.Character.pinnedCharacterFactor P j t))
      (by simpa using Nat.add_le_add hi.2 hj.2)

theorem M6.Normalize.divide_coeff : ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), (M6.Normalize.divide k p).coeff d = p.coeff d / k := by
  classical
  change ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), (M6.Normalize.divide k p).coeff d = p.coeff d / k
  intro k p d
  by_cases hd : d ∈ p.support
  · simp [M6.Normalize.divide, Polynomial.sum, Polynomial.coeff_sum, Polynomial.coeff_monomial, hd]
  · have hz : p.coeff d = 0 := by simpa using hd
    simp [M6.Normalize.divide, Polynomial.sum, Polynomial.coeff_sum, Polynomial.coeff_monomial, hd, hz]

theorem M6.Normalize.scaled_coeff_divisible : ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), k ∣ (Polynomial.C k * p).coeff d := by
  change ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), k ∣ (Polynomial.C k * p).coeff d
  intro k p d
  rw [Polynomial.coeff_C_mul]
  exact ⟨p.coeff d, rfl⟩

theorem M6.Normalize.divide_degree : ∀ (k : ℤ) (p : Polynomial ℤ) (n : ℕ), (∀ d, n < d → p.coeff d = 0) → ∀ d, n < d → (M6.Normalize.divide k p).coeff d = 0 := by
  change ∀ (k : ℤ) (p : Polynomial ℤ) (n : ℕ), (∀ d, n < d → p.coeff d = 0) → ∀ d, n < d → (M6.Normalize.divide k p).coeff d = 0
  intro k p n hp d hd
  rw [M6.Normalize.divide_coeff, hp d hd, Int.zero_ediv]

theorem M6.Normalize.divide_scaled : ∀ (k : ℤ) (p : Polynomial ℤ), k ≠ 0 → M6.Normalize.divide k (Polynomial.C k * p) = p := by
  change ∀ (k : ℤ) (p : Polynomial ℤ), k ≠ 0 → M6.Normalize.divide k (Polynomial.C k * p) = p
  intro k p hk
  apply Polynomial.ext
  intro d
  rw [M6.Normalize.divide_coeff, Polynomial.coeff_C_mul]
  simp [Int.mul_ediv_cancel_left, hk]

theorem M6.ActualTransfer.left_coordinate : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.leftIndex N i) = z.1 i := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.leftIndex N i) = z.1 i
  intro N inst z i
  simp [M6.Flatten.flatten, M6.ActualTransfer.leftIndex, ZMod.val_lt i]

theorem M6.ActualTransfer.right_coordinate : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.rightIndex N i) = z.2 i := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.rightIndex N i) = z.2 i
  intro N inst z i
  have h₁ : ¬ N + i.val < N := by omega
  have h₂ : ¬ i.val + N < N := by omega
  simp [M6.Flatten.flatten, M6.ActualTransfer.rightIndex, h₁, h₂]

theorem M6.ActualTransfer.window_conv : ∀ (R N : ℕ) [NeZero N] (a : M6.ActualTransfer.BP), a.natDegree ≤ R → R < N → ∀ (h : M6.Transfer.Input N) (i : ZMod N), M6.Transfer.cyclicOutput (M6.ActualTransfer.window R a) h i = M6.Physical.conv N (M6.Coordinates.coefficients N a) h i := by
  classical
  intro R N inst a ha hRN h i
  change (∑ j : Fin (R + 1), a.coeff j.val * h (i - (j.val : ZMod N))) =
    ∑ j : ZMod N, a.coeff j.val * h (i - j)
  have hv (j : Fin (R + 1)) : ((j.val : ZMod N)).val = j.val := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt (show j.val < N by omega)]
  calc
    (∑ j : Fin (R + 1), a.coeff j.val * h (i - (j.val : ZMod N))) =
        ∑ j ∈ Finset.univ.filter (fun j : ZMod N => j.val < R + 1),
          a.coeff j.val * h (i - j) := by
      refine Finset.sum_bij (fun j _ => (j.val : ZMod N)) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv]
        exact j.isLt
      · intro j hj k hk hjk
        apply Fin.ext
        have he := congrArg (fun x : ZMod N => x.val) hjk
        simpa only [hv] using he
      · intro j hj
        have hjlt : j.val < R + 1 := (Finset.mem_filter.mp hj).2
        refine ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, ?_⟩
        simp
      · intro j hj
        rw [hv]
    _ = ∑ j : ZMod N, a.coeff j.val * h (i - j) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hjout
      have hjlarge : ¬j.val < R + 1 := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hjout
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show a.natDegree < j.val by omega), zero_mul]

theorem M6.ActualTransfer.product_halves : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (w : Fin (2*N) → ZMod 2 → Polynomial ℤ), (∏ q, w q (M6.Flatten.flatten N z q)) = ∏ i : ZMod N, w (M6.ActualTransfer.leftIndex N i) (z.1 i) * w (M6.ActualTransfer.rightIndex N i) (z.2 i) := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (w : Fin (2*N) → ZMod 2 → Polynomial ℤ), (∏ q, w q (M6.Flatten.flatten N z q)) = ∏ i : ZMod N, w (M6.ActualTransfer.leftIndex N i) (z.1 i) * w (M6.ActualTransfer.rightIndex N i) (z.2 i)
  intro N inst z w
  classical
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    let f : ZMod (n+1) ⊕ ZMod (n+1) → Fin (2*(n+1)) :=
      Sum.elim (M6.ActualTransfer.leftIndex (n+1)) (M6.ActualTransfer.rightIndex (n+1))
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        cases a with
        | inl i =>
          cases b with
          | inl j =>
            have hv := congrArg Fin.val h
            apply congrArg Sum.inl
            apply Fin.ext
            exact hv
          | inr j =>
            have hv := congrArg Fin.val h
            have hi := ZMod.val_lt i
            dsimp [f, M6.ActualTransfer.leftIndex, M6.ActualTransfer.rightIndex] at hv
            omega
        | inr i =>
          cases b with
          | inl j =>
            have hv := congrArg Fin.val h
            have hj := ZMod.val_lt j
            dsimp [f, M6.ActualTransfer.leftIndex, M6.ActualTransfer.rightIndex] at hv
            omega
          | inr j =>
            have hv := congrArg Fin.val h
            apply congrArg Sum.inr
            apply Fin.ext
            dsimp [f, M6.ActualTransfer.rightIndex, ZMod.val] at hv
            omega
      · intro q
        by_cases hq : q.val < n+1
        · refine ⟨Sum.inl (show ZMod (n+1) from (⟨q.val, hq⟩ : Fin (n+1))), ?_⟩
          apply Fin.ext
          rfl
        · have hb : q.val - (n+1) < n+1 := by omega
          refine ⟨Sum.inr (show ZMod (n+1) from (⟨q.val - (n+1), hb⟩ : Fin (n+1))), ?_⟩
          apply Fin.ext
          dsimp [f, M6.ActualTransfer.rightIndex, ZMod.val]
          omega
    let e := Equiv.ofBijective f hf
    have hp := Fintype.prod_equiv e
      (fun s => w (f s) (M6.Flatten.flatten (n+1) z (f s)))
      (fun q => w q (M6.Flatten.flatten (n+1) z q))
      (fun s => rfl)
    rw [← hp, Fintype.prod_sum_type]
    change (∏ i : ZMod (n+1), w (M6.ActualTransfer.leftIndex (n+1) i) (M6.Flatten.flatten (n+1) z (M6.ActualTransfer.leftIndex (n+1) i))) * (∏ i : ZMod (n+1), w (M6.ActualTransfer.rightIndex (n+1) i) (M6.Flatten.flatten (n+1) z (M6.ActualTransfer.rightIndex (n+1) i))) = _
    simp only [M6.ActualTransfer.left_coordinate, M6.ActualTransfer.right_coordinate, Finset.prod_mul_distrib]

theorem M6.ActualTransfer.boundary_input_product : ∀ (R N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), a.natDegree ≤ R → b.natDegree ≤ R → R < N → ∀ (P : M6.Pinned.Pins (2*N)) (h : M6.Transfer.Input N), (∏ i : ZMod N, M6.ActualTransfer.boundaryWeight R N a b P i.val (M6.Transfer.memoryAt h i) (h i)) = M6.Character.pinnedMonomial P (M6.Flatten.flatten N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) := by
  classical
  intro R N inst a b ha hb hRN P h
  rw [← M6.Character.pinned_product, M6.ActualTransfer.product_halves]
  apply Finset.prod_congr rfl
  intro i hi
  simp [M6.ActualTransfer.boundaryWeight, M6.Physical.boundary,
    M6.Transfer.output_convolution,
    M6.ActualTransfer.window_conv R N a ha hRN,
    M6.ActualTransfer.window_conv R N b hb hRN]

theorem M6.ActualTransfer.character_input_product : ∀ (R N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), a.natDegree ≤ R → b.natDegree ≤ R → R < N → ∀ (P : M6.Pinned.Pins (2*N)) (h : M6.Transfer.Input N), (∏ i : ZMod N, M6.ActualTransfer.characterWeight R N a b P i.val (M6.Transfer.memoryAt h i) (h i)) = ∏ q : Fin (2*N), M6.Character.pinnedCharacterFactor P q (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) q) := by
  classical
  intro R N inst a b ha hb hRN P h
  rw [M6.ActualTransfer.product_halves]
  refine Finset.prod_bij (fun i _ => -i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj hij
    exact neg_injective hij
  · intro j hj
    exact ⟨-j, Finset.mem_univ _, neg_neg j⟩
  · intro i hi
    simp [M6.ActualTransfer.characterWeight,
      M6.Transfer.output_convolution,
      M6.ActualTransfer.window_conv R N a ha hRN,
      M6.ActualTransfer.window_conv R N b hb hRN,
      M6.Physical.J, M6.Physical.boundary, M6.Physical.rev, mul_comm]

theorem M6.ActualTransfer.boundary_trace_inputs : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.boundaryTrace N a b P = ∑ h : M6.Transfer.Input N, M6.Character.pinnedMonomial P (M6.Flatten.flatten N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) := by
  intro N inst a b hspan P
  classical
  unfold M6.ActualTransfer.boundaryTrace
  have hdeg : ∀ i m t,
      (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds (2 * N) P _ _ _ _).2
  rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg,
    M6.Transfer.array_trace_inputs]
  apply Finset.sum_congr rfl
  intro h hh
  exact M6.ActualTransfer.boundary_input_product
    (M6.ActualTransfer.span a b) N a b
    (by simpa only [M6.ActualTransfer.span] using (le_max_left a.natDegree b.natDegree))
    (by simpa only [M6.ActualTransfer.span] using (le_max_right a.natDegree b.natDegree))
    hspan P h

theorem M6.ActualTransfer.character_trace_inputs : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.characterTrace N a b P = ∑ h : M6.Transfer.Input N, (∏ q : Fin (2*N), M6.Character.pinnedCharacterFactor P q (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) q)) := by
  intro N inst a b hspan P
  classical
  have hdeg : ∀ i m t,
      (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds (2*N) P _ _ _ _).2
  unfold M6.ActualTransfer.characterTrace
  rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg,
    M6.Transfer.array_trace_inputs]
  apply Finset.sum_congr rfl
  intro h hh
  exact M6.ActualTransfer.character_input_product
    (M6.ActualTransfer.span a b) N a b
    (by unfold M6.ActualTransfer.span; exact le_max_left _ _)
    (by unfold M6.ActualTransfer.span; exact le_max_right _ _)
    hspan P h

theorem M6.ActualCounts.encoded_boundary : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h : M6.Physical.Block N, (M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N a) h), M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N b) h)) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) := by
  intro N inst a b ha hb h
  rw [M6.Coordinates.encode_conv N (M6.Coordinates.coefficients N a) h,
      M6.Coordinates.encode_conv N (M6.Coordinates.coefficients N b) h,
      M6.Coordinates.encode_polynomial N a ha,
      M6.Coordinates.encode_polynomial N b hb]
  rfl

theorem M6.ActualCounts.finite_image_weighted_sum : ∀ (α β : Type) [Fintype α] (L : α → β) (k : ℕ), (∀ a₀ : α, Nat.card {a : α // L a = L a₀} = k) → ∀ w : β → Polynomial ℤ, (∑ a, w (L a)) = Polynomial.C (k : ℤ) * ∑ b ∈ M6.ActualCounts.imageWords L, w b := by
  classical
  intro α β _ L k hk w
  let L' : α → ↥(M6.ActualCounts.imageWords L) := fun a =>
    ⟨L a, by simp [M6.ActualCounts.imageWords]⟩
  have hu : M6.FiberSum.UniformFibers L' k := by
    intro b
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : α, L a₀ = b.val := by
      simpa [M6.ActualCounts.imageWords] using b.property
    have hb : (Finset.univ.filter (fun a : α => L a = b.val)).card = k := by
      simpa [ha₀, Nat.card_eq_fintype_card, Fintype.card_subtype] using hk a₀
    have hf : M6.FiberSum.fiber L' b =
        Finset.univ.filter (fun a : α => L a = b.val) := by
      ext a
      simp only [M6.FiberSum.fiber, Finset.mem_filter, Finset.mem_univ, true_and]
      change (L' a = b ↔ L a = b.val)
      exact Subtype.ext_iff
    change (M6.FiberSum.fiber L' b).card = k
    rw [hf]
    exact hb
  have hs := M6.FiberSum.uniform_weighted_sum α
    ↥(M6.ActualCounts.imageWords L) L' k hu (fun b => w b.val)
  change (∑ a, w (L a)) = Polynomial.C (k : ℤ) *
    (∑ b : ↥(M6.ActualCounts.imageWords L), w b.val) at hs
  rw [Finset.sum_coe_sort] at hs
  exact hs

theorem M6.ActualCounts.boundary_eq_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h h₀ : M6.Physical.Block N, M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀ ↔ M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h₀) := by
  intro N inst a b ha hb h h₀
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro z w e
    have e' := congrArg (M6.Flatten.unflatten N) e
    simpa only [M6.Flatten.flatten_left] using e'
  rw [← M6.ActualCounts.encoded_boundary N a b ha hb h,
      ← M6.ActualCounts.encoded_boundary N a b ha hb h₀]
  simp only [M6.Spaces.boundary_eval, hf.eq_iff,
    M6.Physical.boundary, Prod.mk.injEq,
    (M6.Coordinates.encode_injective N).eq_iff]

theorem M6.ActualCounts.boundary_fiber_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h₀ : M6.Physical.Block N, Nat.card {h : M6.Physical.Block N // M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀} = 2^(M6.ActualCounts.f N a b) := by
  intro N inst a b ha hb h₀
  classical
  let S := {h : M6.Physical.Block N //
    M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h =
    M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀}
  let T := {h : AdjoinRoot (M6.Cyclic.modulus N) //
    M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) h =
    M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h₀)}
  let g : S → T := fun h =>
    ⟨M6.Coordinates.encode N h.val,
      (M6.ActualCounts.boundary_eq_iff N a b ha hb h.val h₀).mp h.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply M6.Coordinates.encode_injective N
      exact congrArg Subtype.val hxy
    · intro y
      obtain ⟨h, hh⟩ := M6.Coordinates.encode_surjective N y.val
      have hp : M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h =
          M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀ := by
        apply (M6.ActualCounts.boundary_eq_iff N a b ha hb h h₀).mpr
        rw [hh]
        exact y.property
      refine ⟨⟨h, hp⟩, ?_⟩
      apply Subtype.ext
      exact hh
  have hc : Nat.card S = Nat.card T :=
    Nat.card_congr (Equiv.ofBijective g hg)
  change Nat.card S = 2 ^ (M6.ActualCounts.f N a b)
  refine hc.trans ?_
  exact M6.BoundaryFibers.fiber_card a b (M6.Cyclic.modulus N)
    (M6.Coordinates.modulus_monic_degree N).1.ne_zero
    (M6.Coordinates.encode N h₀)

theorem M6.ActualCounts.boundary_weighted_sum : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ w : M6.Pinned.Vector (2*N) → Polynomial ℤ, (∑ h : M6.Physical.Block N, w (M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) = Polynomial.C ((2 : ℤ)^(M6.ActualCounts.f N a b)) * ∑ v ∈ M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b), w v := by
  classical
  intro N inst a b ha hb w
  have himage :
      M6.ActualCounts.imageWords (fun h : M6.Physical.Block N =>
        M6.Spaces.boundary N (M6.Coordinates.coefficients N a)
          (M6.Coordinates.coefficients N b) h) =
      M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a)
        (M6.Coordinates.coefficients N b) := by
    ext v
    simp [M6.ActualCounts.imageWords, M6.Spaces.boundary_words_iff,
      M6.Spaces.boundary_eval]
  have hs := M6.ActualCounts.finite_image_weighted_sum
    (M6.Physical.Block N) (M6.Pinned.Vector (2*N))
    (fun h => M6.Spaces.boundary N (M6.Coordinates.coefficients N a)
      (M6.Coordinates.coefficients N b) h)
    (2 ^ M6.ActualCounts.f N a b)
    (M6.ActualCounts.boundary_fiber_card N a b ha hb) w
  simpa [himage] using hs

theorem M6.ActualCounts.dual_boundary_fiber_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h₀ : M6.Physical.Block N, Nat.card {h : M6.Physical.Block N // M6.Spaces.dualBoundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.dualBoundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀} = 2^(M6.ActualCounts.f N a b) := by
  intro N inst a b ha hb h₀
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro z w e
    have e' := congrArg (M6.Flatten.unflatten N) e
    simpa only [M6.Flatten.flatten_left] using e'
  have hj : Function.Injective (M6.Physical.J N) := by
    intro z w e
    have e' := congrArg (M6.Physical.J N) e
    simpa only [M6.Physical.J_involution] using e'
  simpa only [M6.Spaces.dual_boundary_eval, M6.Spaces.boundary_eval,
    hf.eq_iff, hj.eq_iff] using
    (M6.ActualCounts.boundary_fiber_card N a b ha hb h₀)

theorem M6.ActualCounts.boundary_pinned_sum : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ P : M6.Pinned.Pins (2*N), M6.ActualCounts.boundaryInputSum N a b P = Polynomial.C ((2 : ℤ)^(M6.ActualCounts.f N a b)) * M6.Pinned.enumerator (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P := by
  classical
  intro N inst a b ha hb P
  simpa [M6.ActualCounts.boundaryInputSum, M6.Character.pinnedMonomial,
    M6.Pinned.enumerator, Finset.sum_filter, M6.Spaces.boundary_eval] using
    (M6.ActualCounts.boundary_weighted_sum N a b ha hb
      (M6.Character.pinnedMonomial P))

theorem M6.ActualCounts.dual_weighted_sum : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ w : M6.Pinned.Vector (2*N) → Polynomial ℤ, (∑ h : M6.Physical.Block N, w (M6.Spaces.dualBoundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) = Polynomial.C ((2 : ℤ)^(M6.ActualCounts.f N a b)) * ∑ v ∈ M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)), w v := by
  classical
  intro N inst a b ha hb w
  have himage :
      M6.ActualCounts.imageWords
        (fun h : M6.Physical.Block N => M6.Spaces.dualBoundary N
          (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h) =
      M6.Character.subspaceWords (M6.Spaces.D N
        (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) := by
    ext v
    simp [M6.ActualCounts.imageWords, M6.Character.subspaceWords,
      M6.Spaces.D, LinearMap.mem_range]
  have hs := M6.ActualCounts.finite_image_weighted_sum
    (M6.Physical.Block N) (M6.Pinned.Vector (2*N))
    (fun h => M6.Spaces.dualBoundary N
      (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)
    (2 ^ M6.ActualCounts.f N a b)
    (M6.ActualCounts.dual_boundary_fiber_card N a b ha hb) w
  rw [himage] at hs
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs

theorem M6.ActualCounts.input_normalization : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → 2^(M6.ActualCounts.f N a b) * (M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))).card = 2^N := by
  classical
  intro N inst a b ha hb
  have hs := M6.ActualCounts.dual_weighted_sum N a b ha hb
    (fun _ => (1 : Polynomial ℤ))
  have hc : (Fintype.card (M6.Physical.Block N) : ℤ) =
      (2 : ℤ) ^ M6.ActualCounts.f N a b *
        ((M6.Character.subspaceWords (M6.Spaces.D N
          (M6.Coordinates.coefficients N a)
          (M6.Coordinates.coefficients N b))).card : ℤ) := by
    simpa using congrArg (Polynomial.evalRingHom (0 : ℤ)) hs
  have hcard : Fintype.card (M6.Physical.Block N) = 2 ^ N := by
    simpa only [Nat.card_eq_fintype_card] using M6.Spaces.input_card N
  rw [hcard] at hc
  exact_mod_cast hc.symm

theorem M6.ActualCounts.cycle_pinned_sum : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ P : M6.Pinned.Pins (2*N), M6.ActualCounts.signedInputSum N a b P = Polynomial.C ((2 : ℤ)^N) * M6.Pinned.enumerator (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P := by
  classical
  intro N inst a b ha hb P
  have hs := M6.ActualCounts.dual_weighted_sum N a b ha hb
    (fun v => ∏ i, M6.Character.pinnedCharacterFactor P i (v i))
  change M6.ActualCounts.signedInputSum N a b P =
    Polynomial.C ((2 : ℤ) ^ M6.ActualCounts.f N a b) *
      M6.Character.pinnedTransform (M6.Spaces.D N
        (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P at hs
  have hc : (2 : ℤ) ^ M6.ActualCounts.f N a b *
      ((M6.Character.subspaceWords (M6.Spaces.D N
        (M6.Coordinates.coefficients N a)
        (M6.Coordinates.coefficients N b))).card : ℤ) = (2 : ℤ) ^ N := by
    exact_mod_cast M6.ActualCounts.input_normalization N a b ha hb
  rw [← M6.Character.pinned_macwilliams, ← mul_assoc,
    ← Polynomial.C_mul, hc] at hs
  simpa only [M6.Spaces.cycleWords] using hs

theorem M6.ActualCounts.f_le_order : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), M6.ActualCounts.f N a b ≤ N := by
  intro N inst a b
  change (M6.Cyclic.signature a b (M6.Cyclic.modulus N)).natDegree ≤ N
  have hm := M6.Coordinates.modulus_monic_degree N
  have hd := (M6.Cyclic.signature_divides a b (M6.Cyclic.modulus N)).2.2
  simpa only [hm.2] using Polynomial.natDegree_le_of_dvd hd hm.1.ne_zero

theorem M6.ActualCounts.boundary_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(N-(M6.ActualCounts.f N a b)) := by
  intro N inst a b ha hb
  have h := M6.ActualCounts.input_normalization N a b ha hb
  rw [M6.Spaces.dual_boundary_card] at h
  have hf := M6.ActualCounts.f_le_order N a b
  have hexp : M6.ActualCounts.f N a b + (N - M6.ActualCounts.f N a b) = N := by
    omega
  have hpow : (2 : ℕ)^N = 2^(M6.ActualCounts.f N a b) * 2^(N - M6.ActualCounts.f N a b) := by
    rw [← pow_add, hexp]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2 : ℕ)^(M6.ActualCounts.f N a b) by positivity)
  exact h.trans hpow

theorem M6.ActualCounts.boundary_finrank : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → Module.finrank (ZMod 2) (M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = N - (M6.ActualCounts.f N a b) := by
  intro N inst a b ha hb
  classical
  let S := M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
  let e : S ≃ {v // v ∈ M6.Character.subspaceWords S} :=
    { toFun := fun v => ⟨v.1, by simpa [M6.Character.subspaceWords] using v.2⟩
      invFun := fun v => ⟨v.1, by simpa [M6.Character.subspaceWords] using v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card S = (M6.Character.subspaceWords S).card := by
    rw [Nat.card_congr e]
    simp [Nat.card_eq_fintype_card]
  have hp : Nat.card S = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) S :=
    Module.natCard_eq_pow_finrank (K := ZMod 2)
  apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
  change (2 : ℕ) ^ Module.finrank (ZMod 2) S = 2 ^ (N - M6.ActualCounts.f N a b)
  calc
    (2 : ℕ) ^ Module.finrank (ZMod 2) S = Nat.card S := by
      simpa only [Nat.card_zmod] using hp.symm
    _ = (M6.Character.subspaceWords S).card := hc
    _ = 2 ^ (N - M6.ActualCounts.f N a b) := by
      simpa only [S, M6.Spaces.boundaryWords] using
        M6.ActualCounts.boundary_card N a b ha hb

theorem M6.ActualCounts.cycle_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(N+(M6.ActualCounts.f N a b)) := by
  intro N inst a b ha hb
  have h := M6.Character.dual_cardinality (2 * N)
    (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))
  change (M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))).card *
    (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(2 * N) at h
  rw [M6.Spaces.dual_boundary_card, M6.ActualCounts.boundary_card N a b ha hb] at h
  have hf := M6.ActualCounts.f_le_order N a b
  have hexp : (N - M6.ActualCounts.f N a b) + (N + M6.ActualCounts.f N a b) = 2 * N := by
    omega
  have hpow : (2 : ℕ)^(2 * N) = 2^(N - M6.ActualCounts.f N a b) * 2^(N + M6.ActualCounts.f N a b) := by
    rw [← pow_add, hexp]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2 : ℕ)^(N - M6.ActualCounts.f N a b) by positivity)
  exact h.trans hpow

theorem M6.ActualCounts.dual_boundary_finrank : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → Module.finrank (ZMod 2) (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = N - (M6.ActualCounts.f N a b) := by
  intro N inst a b ha hb
  classical
  let S := M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
  let e : S ≃ {v // v ∈ M6.Character.subspaceWords S} :=
    { toFun := fun v => ⟨v.1, by simpa [M6.Character.subspaceWords] using v.2⟩
      invFun := fun v => ⟨v.1, by simpa [M6.Character.subspaceWords] using v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card S = (M6.Character.subspaceWords S).card := by
    rw [Nat.card_congr e]
    simp [Nat.card_eq_fintype_card]
  have hp : Nat.card S = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) S :=
    Module.natCard_eq_pow_finrank (K := ZMod 2)
  apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
  change (2 : ℕ) ^ Module.finrank (ZMod 2) S = 2 ^ (N - M6.ActualCounts.f N a b)
  calc
    (2 : ℕ) ^ Module.finrank (ZMod 2) S = Nat.card S := by
      simpa only [Nat.card_zmod] using hp.symm
    _ = (M6.Character.subspaceWords S).card := hc
    _ = (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card :=
      M6.Spaces.dual_boundary_card N _ _
    _ = 2 ^ (N - M6.ActualCounts.f N a b) :=
      M6.ActualCounts.boundary_card N a b ha hb

theorem M6.ActualCounts.logical_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card : ℤ) = (2 : ℤ)^(N+(M6.ActualCounts.f N a b)) - (2 : ℤ)^(N-(M6.ActualCounts.f N a b)) := by
  intro N inst a b ha hb
  classical
  have hsub := M6.Spaces.boundaries_are_cycles N
    (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
  rw [M6.Spaces.logicalWords, Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub),
    M6.ActualCounts.cycle_card N a b ha hb,
    M6.ActualCounts.boundary_card N a b ha hb]
  norm_cast

theorem M6.ActualCounts.encoded_dimension : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → 2 * N - Module.finrank (ZMod 2) (M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) - Module.finrank (ZMod 2) (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = 2 * (M6.ActualCounts.f N a b) := by
  intro N inst a b ha hb
  rw [M6.ActualCounts.boundary_finrank N a b ha hb,
    M6.ActualCounts.dual_boundary_finrank N a b ha hb]
  have hf := M6.ActualCounts.f_le_order N a b
  omega

theorem M6.ActualCounts.logicals_nonempty_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).Nonempty ↔ 0 < M6.ActualCounts.f N a b) := by
  intro N inst a b ha hb
  classical
  rw [← Finset.card_pos]
  have hc := M6.ActualCounts.logical_card N a b ha hb
  constructor
  · intro hpos
    by_contra h
    have hf0 : M6.ActualCounts.f N a b = 0 := by omega
    simp only [hf0, Nat.add_zero, Nat.sub_zero, sub_self] at hc
    have hpos' : (0 : ℤ) < (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card := by
      exact_mod_cast hpos
    omega
  · intro hf
    have hexp : N - M6.ActualCounts.f N a b < N + M6.ActualCounts.f N a b := by omega
    have hp : (2 : ℤ) ^ (N - M6.ActualCounts.f N a b) < (2 : ℤ) ^ (N + M6.ActualCounts.f N a b) :=
      pow_lt_pow_right₀ (by norm_num) hexp
    have hpos : (0 : ℤ) < (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card := by
      rw [hc]
      exact sub_pos.mpr hp
    exact_mod_cast hpos

theorem M6.ActualCounts.zero_signature_no_logicals : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → M6.ActualCounts.f N a b = 0 → M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) = ∅ := by
  intro N inst a b ha hb hf
  apply Finset.card_eq_zero.mp
  have h := M6.ActualCounts.logical_card N a b ha hb
  simp only [hf, Nat.add_zero, Nat.sub_zero, sub_self] at h
  exact_mod_cast h

theorem M6.Pinned.enumerator_sdiff : ∀ (m : ℕ) (B C : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), B ⊆ C → M6.Pinned.enumerator (C \ B) P = M6.Pinned.enumerator C P - M6.Pinned.enumerator B P := by
  intro m B C P hBC
  classical
  unfold M6.Pinned.enumerator
  apply eq_sub_iff_add_eq.mpr
  exact Finset.sum_sdiff hBC

theorem M6.Pinned.enumerator_total : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), Polynomial.eval 1 (M6.Pinned.enumerator L (M6.Pinned.free m)) = (L.card : ℤ) := by
  classical
  intro m L
  change (Polynomial.evalRingHom (1 : ℤ)) (M6.Pinned.enumerator L (M6.Pinned.free m)) = (L.card : ℤ)
  simp [M6.Pinned.enumerator, M6.Pinned.agrees, M6.Pinned.free]

theorem M6.Pinned.enumerator_zero_coeff : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), (0 : M6.Pinned.Vector m) ∉ L → (M6.Pinned.enumerator L P).coeff 0 = 0 := by
  classical
  intro m L P hzero
  rw [M6.Pinned.enumerator_coeff]
  obtain ⟨hnonneg, hpos⟩ := M6.Pinned.count_nonnegative_positive m L P 0
  apply le_antisymm _ hnonneg
  apply le_of_not_gt
  intro h
  obtain ⟨v, hvL, _, hw⟩ := hpos.mp h
  have hvzero : v = 0 := by
    funext i
    change v i = 0
    by_contra hi
    unfold M6.Pinned.weight at hw
    have hempty := Finset.card_eq_zero.mp hw
    have hmem : i ∈ Finset.univ.filter (fun j : Fin m => v j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    rw [hempty] at hmem
    simpa using hmem
  exact hzero (hvzero ▸ hvL)

theorem M6.ActualResult.boundary_normalized : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  have ha : a.natDegree < N :=
    lt_of_le_of_lt (le_max_left a.natDegree b.natDegree) h
  have hb : b.natDegree < N :=
    lt_of_le_of_lt (le_max_right a.natDegree b.natDegree) h
  have ha' : a.degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast ha)
  have hb' : b.degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hb)
  rw [M6.ActualTransfer.boundary_trace_inputs N a b h P]
  have hs := M6.ActualCounts.boundary_pinned_sum N a b ha' hb' P
  calc
    _ = M6.Normalize.divide ((2 : ℤ) ^ M6.ActualCounts.f N a b)
        (Polynomial.C ((2 : ℤ) ^ M6.ActualCounts.f N a b) *
          M6.Pinned.enumerator (M6.Spaces.boundaryWords N
            (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P) :=
      congrArg (M6.Normalize.divide ((2 : ℤ) ^ M6.ActualCounts.f N a b)) hs
    _ = _ := M6.Normalize.divide_scaled _ _ (pow_ne_zero _ (by norm_num))

theorem M6.ActualResult.cycle_normalized : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualTransfer.characterTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualTransfer.characterTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  have ha : a.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_left a.natDegree b.natDegree) h : a.natDegree < N)
  have hb : b.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_right a.natDegree b.natDegree) h : b.natDegree < N)
  rw [M6.ActualTransfer.character_trace_inputs N a b h P]
  change M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualCounts.signedInputSum N a b P) = _
  rw [M6.ActualCounts.cycle_pinned_sum N a b ha hb P]
  exact M6.Normalize.divide_scaled _ _ (pow_ne_zero N (by norm_num))

theorem M6.ActualResult.Q_enumerator : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.Q N a b P = M6.Pinned.enumerator (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.Q N a b P = M6.Pinned.enumerator (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  unfold M6.ActualTransfer.Q
  change M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualTransfer.characterTrace N a b P) - M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = _
  rw [M6.ActualResult.cycle_normalized N a b h P, M6.ActualResult.boundary_normalized N a b h P]
  unfold M6.Spaces.logicalWords
  symm
  apply M6.Pinned.enumerator_sdiff <;> exact M6.Spaces.boundaries_are_cycles N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)

theorem M6.ActualResult.Q_coeff : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ (P : M6.Pinned.Pins (2*N)) (d : ℕ), (M6.ActualTransfer.Q N a b P).coeff d = M6.Pinned.count (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P d ∧ 0 ≤ (M6.ActualTransfer.Q N a b P).coeff d := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ (P : M6.Pinned.Pins (2*N)) (d : ℕ), (M6.ActualTransfer.Q N a b P).coeff d = M6.Pinned.count (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P d ∧ 0 ≤ (M6.ActualTransfer.Q N a b P).coeff d
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P d
  rw [M6.ActualResult.Q_enumerator N a b h P, M6.Pinned.enumerator_coeff (2*N)]
  exact ⟨rfl, (M6.Pinned.count_nonnegative_positive (2*N) _ P d).1⟩

theorem M6.ActualResult.Q_total : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → Polynomial.eval 1 (M6.ActualTransfer.Q N a b (M6.Pinned.free (2*N))) = ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card : ℤ) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → Polynomial.eval 1 (M6.ActualTransfer.Q N a b (M6.Pinned.free (2*N))) = ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card : ℤ)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h
  rw [M6.ActualResult.Q_enumerator N a b h]
  exact M6.Pinned.enumerator_total _ _

theorem M6.ActualResult.Q_zero : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), (M6.ActualTransfer.Q N a b P).coeff 0 = 0 := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), (M6.ActualTransfer.Q N a b P).coeff 0 = 0
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P
  rw [M6.ActualResult.Q_enumerator N a b h P]
  apply M6.Pinned.enumerator_zero_coeff
  exact M6.Spaces.zero_not_logical N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)

theorem M6.ActualResult.solve_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → (M6.ActualTransfer.solve N a b = none ↔ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) → v ∈ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)), d ≤ M6.Pinned.weight u) ∧ k ≤ 2*N := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → (M6.ActualTransfer.solve N a b = none ↔ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = ∅) ∧ ∀ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) → v ∈ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) ∧ M6.Pinned.weight v = d ∧ (∀ u ∈ (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)), d ≤ M6.Pinned.weight u) ∧ k ≤ 2*N
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h
  exact M6.Pinned.solve_exact (2 * N)
    (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a)
      (M6.Coordinates.coefficients N b))
    (M6.ActualTransfer.Q N a b)
    (M6.ActualResult.Q_enumerator N a b h)

theorem M6.FixedSpan.distance_improvement : ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^3 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0) := by
  change ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^3 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)
  intro R
  have h := tendsto_pow_const_div_const_pow_of_one_lt 3 (r := (4 : ℝ)) (by norm_num)
  simpa only [zero_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h.mul_const ((4 : ℝ)^R)

theorem M6.FixedSpan.recipe_degree : M6.FixedSpan.recipe.Monic ∧ M6.FixedSpan.recipe.natDegree = 2 := by
  change M6.FixedSpan.recipe.Monic ∧ M6.FixedSpan.recipe.natDegree = 2
  unfold M6.FixedSpan.recipe
  constructor
  · monicity!
  · compute_degree!

theorem M6.FixedSpan.recipe_divides : ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N := by
  change ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N
  intro N hN
  obtain ⟨k, rfl⟩ := hN
  have htwo : (2 : M6.Cyclic.BinaryPolynomial) = 0 :=
    CharP.cast_eq_zero M6.Cyclic.BinaryPolynomial 2
  have hneg : -(1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    calc
      -(1 : M6.Cyclic.BinaryPolynomial) = -1 + 2 := by rw [htwo]; simp
      _ = 1 := by ring
  have hfactor : M6.FixedSpan.recipe ∣ (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ 3 - 1 := by
    refine ⟨Polynomial.X + 1, ?_⟩
    symm
    calc
      M6.FixedSpan.recipe * (Polynomial.X + 1) =
          Polynomial.X ^ 3 + 1 + (2 : M6.Cyclic.BinaryPolynomial) *
            (Polynomial.X ^ 2 + Polynomial.X) := by
        unfold M6.FixedSpan.recipe
        ring
      _ = Polynomial.X ^ 3 - 1 := by
        rw [htwo]
        simp [sub_eq_add_neg, hneg]
  apply dvd_trans hfactor
  simpa [M6.Cyclic.modulus, pow_mul, sub_eq_add_neg, hneg] using
    (sub_dvd_pow_sub_pow ((Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ 3) 1 k)

theorem M6.FixedSpan.recipe_support : M6.FixedSpan.recipe.support = {0,1,2} := by
  classical
  change M6.FixedSpan.recipe.support = {0, 1, 2}
  ext n
  by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;> by_cases h2 : n = 2 <;>
    simp_all [M6.FixedSpan.recipe, Polynomial.mem_support_iff,
      Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow, eq_comm]

theorem M6.FixedSpan.witness_improvement : ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^4 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0) := by
  change ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^4 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)
  intro R
  have h := tendsto_pow_const_div_const_pow_of_one_lt 4 (r := (4 : ℝ)) (by norm_num)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h.mul_const ((4 : ℝ)^R)

theorem M6.FixedSpan.recipe_signature : ∀ N : ℕ, 3 ∣ N → M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N) = M6.FixedSpan.recipe := by
  change ∀ N : ℕ, 3 ∣ N → M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N) = M6.FixedSpan.recipe
  intro N hN
  simp [M6.Cyclic.signature, EuclideanDomain.gcd_self, EuclideanDomain.gcd_eq_left, M6.FixedSpan.recipe_divides N hN]

theorem M6.FixedSpan.nontrivial_family : ∀ k : ℕ, let N := 3*(k+1); 2 < N ∧ M6.FixedSpan.recipe.support.card = 3 ∧ 0 ∈ M6.FixedSpan.recipe.support ∧ Nat.gcd N (M6.FixedSpan.recipe.support.gcd id) = 1 ∧ (M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N)).natDegree = 2 := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ k : ℕ, let N := 3*(k+1); 2 < N ∧ M6.FixedSpan.recipe.support.card = 3 ∧ 0 ∈ M6.FixedSpan.recipe.support ∧ Nat.gcd N (M6.FixedSpan.recipe.support.gcd id) = 1 ∧ (M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N)).natDegree = 2
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro k
  dsimp only
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [M6.FixedSpan.recipe_support]
    decide
  · rw [M6.FixedSpan.recipe_support]
    decide
  · rw [M6.FixedSpan.recipe_support]
    have hg : ({0, 1, 2} : Finset ℕ).gcd id = 1 := by decide
    rw [hg]
    simp
  · rw [M6.FixedSpan.recipe_signature (3 * (k + 1)) ⟨k + 1, rfl⟩]
    exact M6.FixedSpan.recipe_degree.2

theorem M6.ZeroSpan.anchored_zero : ∀ (a b : M6.Final.BP), a.coeff 0 = 1 → b.coeff 0 = 1 → M6.ActualTransfer.span a b = 0 → a = 1 ∧ b = 1 := by
  change ∀ (a b : M6.Final.BP), a.coeff 0 = 1 → b.coeff 0 = 1 → M6.ActualTransfer.span a b = 0 → a = 1 ∧ b = 1
  intro a b ha hb hspan
  change max a.natDegree b.natDegree = 0 at hspan
  have hda : a.natDegree = 0 := by omega
  have hdb : b.natDegree = 0 := by omega
  constructor
  · simpa [ha] using (Polynomial.eq_C_of_natDegree_eq_zero hda)
  · simpa [hb] using (Polynomial.eq_C_of_natDegree_eq_zero hdb)

theorem M6.ZeroSpan.boundary_loops : ∀ (N : ℕ) [NeZero N] (i : ℕ) (m n : M6.Transfer.Memory 0), M6.Transfer.edgeMatrix (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N)) i) m n = (1 : Polynomial ℤ) + Polynomial.X^2 := by
  classical
  intro N _ i m n
  have hs : ∀ t : M6.Transfer.Bit, M6.Transfer.shift m t = n := fun _ => Subsingleton.elim _ _
  have hu : (Finset.univ : Finset M6.Transfer.Bit) = {0, 1} := by decide
  simp only [M6.Transfer.edgeMatrix, hs, if_true, hu, Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton, zero_ne_one, not_false_eq_true]
  simp [M6.ActualTransfer.boundaryWeight, M6.ActualTransfer.window, M6.Character.boundaryFactor, M6.Pinned.free]
  first
  | simp [M6.Transfer.localOutput, M6.ActualTransfer.window, pow_two]
  | simp [M6.Transfer.output, M6.ActualTransfer.window, pow_two]
  all_goals norm_num [ZMod.val_one, pow_two]

theorem M6.ZeroSpan.character_loops : ∀ (N : ℕ) [NeZero N] (i : ℕ) (m n : M6.Transfer.Memory 0), M6.Transfer.edgeMatrix (M6.ActualTransfer.characterWeight 0 N 1 1 (M6.Pinned.free (2*N)) i) m n = Polynomial.C 2 * ((1 : Polynomial ℤ) + Polynomial.X^2) := by
  classical
  intro N hN i m n
  have heq : ∀ a b : M6.Transfer.Memory 0, a = b ↔ True := by
    intro a b
    exact iff_true_intro (Subsingleton.elim a b)
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    decide
  have hout : ∀ t : ZMod 2, M6.Transfer.output (M6.ActualTransfer.window 0 1) m t = t := by
    intro t
    simp [M6.Transfer.output, M6.ActualTransfer.window]
  have hv : (1 : ZMod 2).val = 1 := rfl
  simp [M6.Transfer.edgeMatrix, heq, hu, M6.ActualTransfer.characterWeight,
    hout, M6.Character.free_character_factor, M6.Character.sign, hv]
  <;> ring

theorem M6.ZeroSpan.connected_zero : ∀ N : ℕ, M6.Final.Admissible N 1 1 → N = 1 := by
  intro N h
  rcases h with ⟨_, _, _, _, _, hg⟩
  have hs : (1 : M6.Final.BP).support = {0} := by
    change (Polynomial.C (1 : ZMod 2)).support = {0}
    exact Polynomial.support_C (one_ne_zero : (1 : ZMod 2) ≠ 0)
  simpa [hs] using hg

theorem M6.ZeroSpan.signature_one : ∀ N : ℕ, M6.Cyclic.signature 1 1 (M6.Cyclic.modulus N) = 1 := by
  change ∀ N : ℕ, M6.Cyclic.signature 1 1 (M6.Cyclic.modulus N) = 1
  intro N
  simp [M6.Cyclic.signature]

theorem M6.ZeroSpan.zero_memory_trace : ∀ (N : ℕ) (W : ℕ → M6.Transfer.Memory 0 → M6.Transfer.Bit → Polynomial ℤ) (p : Polynomial ℤ), (∀ i m n, M6.Transfer.edgeMatrix (W i) m n = p) → M6.Transfer.arrayTrace W N = p^N := by
  change ∀ (N : ℕ) (W : ℕ → M6.Transfer.Memory 0 → M6.Transfer.Bit → Polynomial ℤ) (p : Polynomial ℤ), (∀ i m n, M6.Transfer.edgeMatrix (W i) m n = p) → M6.Transfer.arrayTrace W N = p ^ N
  intro N W p h
  classical
  haveI : Subsingleton (M6.Transfer.Memory 0) := ⟨fun a b => funext fun i => Fin.elim0 i⟩
  letI : Unique (M6.Transfer.Memory 0) :=
    { default := fun i => Fin.elim0 i
      uniq := fun m => Subsingleton.elim _ _ }
  have hp : ∀ n (m k : M6.Transfer.Memory 0),
      M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) n m k = p ^ n := by
    intro n
    induction n with
    | zero =>
        intro m k
        simp [M6.Transfer.matrixProduct, Matrix.one_apply, Subsingleton.elim m k]
    | succ n ih =>
        intro m k
        simp [M6.Transfer.matrixProduct, Matrix.mul_apply, ih, h, pow_succ, mul_comm]
  rw [M6.Transfer.array_trace_matrix 0 (Polynomial ℤ) W N]
  simp [Matrix.trace, Matrix.diag, hp]

theorem M6.ZeroSpan.boundary_trace_zero : ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.boundaryTrace N 1 1 (M6.Pinned.free (2*N)) = ((1 : Polynomial ℤ) + Polynomial.X^2)^N := by
  change ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.boundaryTrace N 1 1 (M6.Pinned.free (2*N)) = ((1 : Polynomial ℤ) + Polynomial.X^2)^N
  intro N _
  classical
  have hs : M6.ActualTransfer.span 1 1 = 0 := by
    simp [M6.ActualTransfer.span]
  unfold M6.ActualTransfer.boundaryTrace
  rw [hs]
  trans M6.Transfer.arrayTrace (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N))) N
  · apply M6.Transfer.scalar_trace_polynomial
    intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds (2*N) (M6.Pinned.free (2*N)) _ _ _ _).2
  · exact M6.ZeroSpan.zero_memory_trace N _ _ (M6.ZeroSpan.boundary_loops N)

theorem M6.ZeroSpan.character_trace_zero : ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.characterTrace N 1 1 (M6.Pinned.free (2*N)) = Polynomial.C ((2 : ℤ)^N) * ((1 : Polynomial ℤ) + Polynomial.X^2)^N := by
  change ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.characterTrace N 1 1 (M6.Pinned.free (2*N)) = Polynomial.C ((2 : ℤ)^N) * ((1 : Polynomial ℤ) + Polynomial.X^2)^N
  intro N hN
  classical
  have hs : M6.ActualTransfer.span 1 1 = 0 := by
    simp [M6.ActualTransfer.span]
  have hb : ∀ i m t,
      (M6.ActualTransfer.characterWeight 0 N 1 1 (M6.Pinned.free (2*N)) i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).2
  unfold M6.ActualTransfer.characterTrace
  rw [hs]
  rw [M6.Transfer.scalar_trace_polynomial 0 N _ hb]
  rw [M6.ZeroSpan.zero_memory_trace N _
    (Polynomial.C 2 * ((1 : Polynomial ℤ) + Polynomial.X^2))
    (M6.ZeroSpan.character_loops N)]
  rw [mul_pow, ← Polynomial.C_pow]

theorem M6.Transfer.address_width : ∀ R N : ℕ, 0 < N → M6.Transfer.addressLocations R N ≤ 2^(M6.Transfer.addressBits R N) := by
  change ∀ R N : ℕ, 0 < N → M6.Transfer.addressLocations R N ≤ 2 ^ (M6.Transfer.addressBits R N)
  intro R N hN
  have hbound : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      omega
  have hsquare : (N + 1) ^ 2 ≤ (2 ^ N) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (hbound N) (hbound N)
  change 16 * 2 ^ R * (N + 1) ^ 2 ≤ 2 ^ (R + 2 * N + 4)
  calc
    16 * 2 ^ R * (N + 1) ^ 2 ≤ 16 * 2 ^ R * (2 ^ N) ^ 2 :=
      Nat.mul_le_mul_left _ hsquare
    _ = 2 ^ (R + 2 * N + 4) := by
      rw [pow_add, pow_add, Nat.mul_comm 2 N, pow_mul]
      ring

theorem M6.Transfer.coefficient_width : ∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N) := by
  change ∀ R N : ℕ, 2^R * 8^N < 2^(R + 3*N + 2)
  intro R N
  have h : 0 < (2 : ℕ)^R * 8^N := by positivity
  norm_num [pow_add, pow_mul] <;> nlinarith

theorem M6.Transfer.state_count : ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2^R := by
  change ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2 ^ R
  intro R
  simp [M6.Transfer.Memory, M6.Transfer.Bit, Fintype.card_fun, ZMod.card]

theorem M6.Transfer.trace_storage_bound : ∀ R N : ℕ, R < N → M6.Transfer.traceStorageModel R N ≤ 128 * N^2 * 2^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.traceStorageModel R N ≤ 128 * N^2 * 2^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hp : 1 ≤ (2 : ℕ)^R := by
    have : 0 < (2 : ℕ)^R := by positivity
    omega
  have hc : M6.Transfer.coefficientBits R N ≤ 6*N := by
    unfold M6.Transfer.coefficientBits
    omega
  have hs : 2*N+1 ≤ 3*N := by omega
  have hr : R+2 ≤ 3*N := by omega
  have h1 : 2 * 2^R * (2*N+1) * M6.Transfer.coefficientBits R N ≤ 36 * N^2 * 2^R := by
    calc
      2 * 2^R * (2*N+1) * M6.Transfer.coefficientBits R N
          ≤ 2 * 2^R * (3*N) * (6*N) := by gcongr
      _ = 36 * N^2 * 2^R := by ring
  have h2 : (2*N+1) * M6.Transfer.coefficientBits R N ≤ 18 * N^2 := by
    calc
      (2*N+1) * M6.Transfer.coefficientBits R N ≤ (3*N) * (6*N) := by gcongr
      _ = 18 * N^2 := by ring
  have h3 : 2 * 2^R * (R+2) ≤ 6 * N * 2^R := by
    calc
      2 * 2^R * (R+2) ≤ 2 * 2^R * (3*N) := by gcongr
      _ = 6 * N * 2^R := by ring
  have hn2 : N ≤ N^2 := by nlinarith
  have hb : N^2 ≤ N^2 * 2^R := by
    simpa using Nat.mul_le_mul_left (N^2) hp
  have hnp : N * 2^R ≤ N^2 * 2^R :=
    Nat.mul_le_mul_right (2^R) hn2
  have hnT : N ≤ N^2 * 2^R := le_trans hn2 hb
  have hT : 1 ≤ N^2 * 2^R := le_trans hN hnT
  unfold M6.Transfer.traceStorageModel
  nlinarith

theorem M6.Transfer.scatter_loop_count : ∀ R N : ℕ, M6.Transfer.traceCoefficientOps R N = 6 * N * (2*N+1) * 4^R := by
  change ∀ R N : ℕ, M6.Transfer.traceCoefficientOps R N = 6 * N * (2 * N + 1) * 4 ^ R
  intro R N
  simp only [M6.Transfer.traceCoefficientOps, M6.Transfer.ScatterEvent,
    Fintype.card_prod, M6.Transfer.state_count, Fintype.card_fin,
    M6.Transfer.Bit, ZMod.card]
  have hpow : (4 : ℕ) ^ R = 2 ^ R * 2 ^ R := by
    simpa using (mul_pow (2 : ℕ) 2 R)
  rw [hpow]
  ring

theorem M6.Transfer.trace_work_bound : ∀ R N : ℕ, R < N → M6.Transfer.traceWorkModel R N ≤ 4096 * N^3 * 4^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.traceWorkModel R N ≤ 4096 * N^3 * 4^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hslots : 2 * N + 1 ≤ 3 * N := by omega
  have hcharge : M6.Transfer.eventBitCharge R N ≤ 60 * N := by
    unfold M6.Transfer.eventBitCharge M6.Transfer.coefficientBits M6.Transfer.addressBits
    omega
  have hpow : ((2 : ℕ)^R)^2 = 4^R := by
    calc
      (2^R)^2 = 2^R * 2^R := by ring
      _ = (2 * 2)^R := (mul_pow (2 : ℕ) 2 R).symm
      _ = 4^R := by norm_num
  have hcount : M6.Transfer.traceCoefficientOps R N + (2^R)^2 * N * (2*N+1) ≤ 21 * N^2 * 4^R := by
    rw [M6.Transfer.scatter_loop_count, hpow]
    calc
      6 * N * (2*N+1) * 4^R + 4^R * N * (2*N+1)
          = (7 * N * 4^R) * (2*N+1) := by ring
      _ ≤ (7 * N * 4^R) * (3*N) := Nat.mul_le_mul_left _ hslots
      _ = 21 * N^2 * 4^R := by ring
  unfold M6.Transfer.traceWorkModel
  calc
    (M6.Transfer.traceCoefficientOps R N + (2^R)^2 * N * (2*N+1)) * M6.Transfer.eventBitCharge R N
        ≤ (21 * N^2 * 4^R) * (60*N) := Nat.mul_le_mul hcount hcharge
    _ = 1260 * (N^3 * 4^R) := by ring
    _ ≤ 4096 * (N^3 * 4^R) := Nat.mul_le_mul_right _ (by decide : (1260 : ℕ) ≤ 4096)
    _ = 4096 * N^3 * 4^R := by ring

theorem M6.Transfer.actual_trace_intermediates : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (k : ℕ) (d : Fin (2*N+1)), (∀ j m t, M6.Transfer.polynomialMass (W j m t) ≤ 4) → (∀ j m t, (W j m t).natDegree ≤ 2) → ((((Finset.univ : Finset (M6.Transfer.Memory R)).toList.take k).map (fun start => M6.Transfer.scalarLayers (N:=N) W start N (start,d))).sum).natAbs ≤ 2^R * 8^N := by
  classical
  intro R N W k d hmass hdeg
  have hterm (start : M6.Transfer.Memory R) :
      (M6.Transfer.scalarLayers (N := N) W start N (start, d)).natAbs ≤ 8^N := by
    rw [M6.Transfer.scalar_layers_exact R N W start N hdeg]
    change ((M6.Transfer.layers W start N start).coeff d.val).natAbs ≤ 8^N
    calc
      _ ≤ M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) :=
        M6.Transfer.mass_basic.2.2.2 _ _
      _ ≤ M6.Transfer.rowMass (M6.Transfer.layers W start N) := by
        unfold M6.Transfer.rowMass
        exact Finset.single_le_sum
          (f := fun m => M6.Transfer.polynomialMass (M6.Transfer.layers W start N m))
          (fun m _ => Nat.zero_le _) (Finset.mem_univ start)
      _ ≤ 8^N := M6.Transfer.layers_mass R W start N hmass
  have hlist (l : List (M6.Transfer.Memory R)) :
      ((l.map (fun start => M6.Transfer.scalarLayers (N := N) W start N (start, d))).sum).natAbs
        ≤ l.length * 8^N := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ (M6.Transfer.scalarLayers (N := N) W a N (a, d)).natAbs +
            ((l.map (fun start => M6.Transfer.scalarLayers (N := N) W start N (start, d))).sum).natAbs :=
          Int.natAbs_add_le _ _
        _ ≤ 8^N + l.length * 8^N := Nat.add_le_add (hterm a) ih
        _ = (l.length + 1) * 8^N := by simp [Nat.add_mul, Nat.add_comm]
  have hlen :
      (((Finset.univ : Finset (M6.Transfer.Memory R)).toList).take k).length ≤ 2^R := by
    calc
      _ ≤ (Finset.univ : Finset (M6.Transfer.Memory R)).toList.length := by
        simp only [List.length_take]
        exact Nat.min_le_right _ _
      _ = 2^R := by simp [M6.Transfer.state_count]
  exact (hlist _).trans (Nat.mul_le_mul_right (8^N) hlen)

theorem M6.Transfer.finite_coefficient_mass : ∀ (p : Polynomial ℤ) (L : ℕ), (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ M6.Transfer.polynomialMass p := by
  classical
  change ∀ (p : Polynomial ℤ) (L : ℕ), (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ M6.Transfer.polynomialMass p
  intro p L
  change (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ ∑ d ∈ p.support, (p.coeff d).natAbs
  have hfin : (∑ d : Fin L, (p.coeff d.val).natAbs) = ∑ d ∈ Finset.range L, (p.coeff d).natAbs :=
    Fin.sum_univ_eq_sum_range (fun d : ℕ => (p.coeff d).natAbs) L
  rw [hfin]
  calc
    (∑ d ∈ Finset.range L, (p.coeff d).natAbs) ≤
        ∑ d ∈ p.support ∪ Finset.range L, (p.coeff d).natAbs := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_union_right
      · intros
        exact Nat.zero_le _
    _ = ∑ d ∈ p.support, (p.coeff d).natAbs := by
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro d hd hnot
      have hz : p.coeff d = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hnot
      simp [hz]

theorem M6.Transfer.encoded_array_mass : ∀ (R N : ℕ) (v : M6.Transfer.Memory R → Polynomial ℤ), M6.Transfer.arrayMass (M6.Transfer.encodeCoefficients (N:=N) v) ≤ M6.Transfer.rowMass v := by
  classical
  change ∀ (R N : ℕ) (v : M6.Transfer.Memory R → Polynomial ℤ), M6.Transfer.arrayMass (M6.Transfer.encodeCoefficients (N := N) v) ≤ M6.Transfer.rowMass v
  intro R N v
  change (∑ addr : M6.Transfer.Memory R × Fin (2 * N + 1), ((v addr.1).coeff addr.2.val).natAbs) ≤ ∑ m : M6.Transfer.Memory R, M6.Transfer.polynomialMass (v m)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro m hm
  exact M6.Transfer.finite_coefficient_mass (v m) (2 * N + 1)

theorem M6.Transfer.event_mass_bound : ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.eventMass W input ≤ 8 * M6.Transfer.arrayMass input := by
  classical
  change ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.eventMass W input ≤ 8 * M6.Transfer.arrayMass input
  intro R N W input hW
  unfold M6.Transfer.eventMass M6.Transfer.arrayMass
  simp only [M6.Transfer.ScatterEvent, M6.Transfer.CoefficientAddress,
    Fintype.sum_prod_type, M6.Transfer.eventTerm, Int.natAbs_mul]
  calc
    _ ≤ ∑ m : M6.Transfer.Memory R, ∑ t : M6.Transfer.Bit,
        ∑ i : Fin (2 * N + 1), (input (m, i)).natAbs * 4 := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _
        ((M6.Transfer.finite_coefficient_mass (W m t) 3).trans (hW m t))
    _ = _ := by
      simp [M6.Transfer.Bit, ← Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] <;> ring

theorem M6.Transfer.scatter_prefix_magnitude : ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N) (k : ℕ) (addr : M6.Transfer.CoefficientAddress R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → (((M6.Transfer.scatterEventList R N).take k).foldl (M6.Transfer.scatterUpdate W input) (fun _ => 0) addr).natAbs ≤ 8 * M6.Transfer.arrayMass input := by
  classical
  change ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N) (k : ℕ) (addr : M6.Transfer.CoefficientAddress R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → (((M6.Transfer.scatterEventList R N).take k).foldl (M6.Transfer.scatterUpdate W input) (fun _ => 0) addr).natAbs ≤ 8 * M6.Transfer.arrayMass input
  intro R N W input k addr hW
  let f : M6.Transfer.ScatterEvent R N → ℤ := fun e =>
    if M6.Transfer.eventDestination e = some addr then M6.Transfer.eventTerm W input e else 0
  let g : M6.Transfer.ScatterEvent R N → ℕ := fun e =>
    (M6.Transfer.eventTerm W input e).natAbs
  have hf (e : M6.Transfer.ScatterEvent R N) : (f e).natAbs ≤ g e := by
    dsimp [f, g]
    split <;> simp
  have hlist (l : List (M6.Transfer.ScatterEvent R N)) (j : ℕ) :
      (((l.take j).map f).sum).natAbs ≤ (l.map g).sum := by
    induction l generalizing j with
    | nil => simp
    | cons e l ih =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (hf e) (ih j))
  rw [M6.Transfer.scatter_prefix_formula, zero_add]
  change ((((M6.Transfer.scatterEventList R N).take k).map f).sum).natAbs ≤ _
  apply (hlist (M6.Transfer.scatterEventList R N) k).trans
  simpa [M6.Transfer.scatterEventList, g, M6.Transfer.eventMass] using
    (M6.Transfer.event_mass_bound R N W input hW)

theorem M6.Transfer.actual_layer_intermediates : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start : M6.Transfer.Memory R) (i k : ℕ) (addr : M6.Transfer.CoefficientAddress R N), (∀ j m t, M6.Transfer.polynomialMass (W j m t) ≤ 4) → (∀ j m t, (W j m t).natDegree ≤ 2) → ((((M6.Transfer.scatterEventList R N).take k).foldl (M6.Transfer.scatterUpdate (W i) (M6.Transfer.scalarLayers (N:=N) W start i)) (fun _ => 0) addr).natAbs ≤ 8^(i+1)) ∧ (∀ e : M6.Transfer.ScatterEvent R N, (M6.Transfer.eventTerm (W i) (M6.Transfer.scalarLayers (N:=N) W start i) e).natAbs ≤ 8^(i+1)) := by
  classical
  intro R N W start i k addr hmass hdegree
  have hinput : M6.Transfer.arrayMass (M6.Transfer.scalarLayers (N := N) W start i) ≤ 8 ^ i := by
    rw [M6.Transfer.scalar_layers_exact R N W start i hdegree]
    exact (M6.Transfer.encoded_array_mass R N (M6.Transfer.layers W start i)).trans
      (M6.Transfer.layers_mass R W start i hmass)
  have hbound : 8 * M6.Transfer.arrayMass (M6.Transfer.scalarLayers (N := N) W start i) ≤ 8 ^ (i + 1) := by
    calc
      _ ≤ 8 * 8 ^ i := Nat.mul_le_mul_left 8 hinput
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  constructor
  · exact (M6.Transfer.scatter_prefix_magnitude R N (W i)
      (M6.Transfer.scalarLayers (N := N) W start i) k addr (hmass i)).trans hbound
  · intro e
    have he : (M6.Transfer.eventTerm (W i)
        (M6.Transfer.scalarLayers (N := N) W start i) e).natAbs ≤
        M6.Transfer.eventMass (W i) (M6.Transfer.scalarLayers (N := N) W start i) := by
      unfold M6.Transfer.eventMass
      exact Finset.single_le_sum
        (f := fun e : M6.Transfer.ScatterEvent R N =>
          (M6.Transfer.eventTerm (W i)
            (M6.Transfer.scalarLayers (N := N) W start i) e).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    exact he.trans ((M6.Transfer.event_mass_bound R N (W i)
      (M6.Transfer.scalarLayers (N := N) W start i) (hmass i)).trans hbound)

theorem M6.Transfer.actual_signed_capacity : ∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N - 1) := by
  change ∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N - 1)
  intro R N
  change 2^R * 8^N < 2^(R + 3*N + 2 - 1)
  have h : R + 3*N + 2 - 1 = R + 3*N + 1 := by omega
  rw [h, show (8 : ℕ) = 2^3 by norm_num, ← pow_mul, ← pow_add, pow_succ]
  have hp : 0 < (2 : ℕ)^(R + 3*N) := by positivity
  omega

theorem M6.Transfer.actual_trace_storage_bound : ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hspos : 0 < (2 : ℕ)^R := by positivity
  have hs : 1 ≤ (2 : ℕ)^R := by omega
  have hNN : N ≤ N^2 := by nlinarith
  have hscale : N ≤ N^2 * 2^R := by
    calc
      N ≤ N^2 := hNN
      _ = N^2 * 1 := by simp
      _ ≤ N^2 * 2^R := Nat.mul_le_mul_left _ hs
  have haddr : M6.Transfer.actualAddressBits R N ≤ 21*N := by
    unfold M6.Transfer.actualAddressBits
    omega
  have hcoeff : M6.Transfer.coefficientBits R N ≤ 6*N := by
    unfold M6.Transfer.coefficientBits
    omega
  have hlen : (M6.Transfer.scatterEventList R N).length = 6*(2*N+1)*2^R := by
    simp [M6.Transfer.scatterEventList, M6.Transfer.ScatterEvent,
      Fintype.card_prod, M6.Transfer.Bit, M6.Transfer.state_count,
      mul_assoc, mul_comm, mul_left_comm] <;> ring
  have hslots : 2*N+1 ≤ 3*N := by omega
  have hlenbound : (M6.Transfer.scatterEventList R N).length ≤ 18*N*2^R := by
    rw [hlen]
    nlinarith [Nat.mul_le_mul_right (6*2^R) hslots]
  have hrecord : 4*M6.Transfer.actualAddressBits R N+8 ≤ 92*N := by omega
  have hevents : (M6.Transfer.scatterEventList R N).length *
      (4*M6.Transfer.actualAddressBits R N+8) ≤ 1656*N^2*2^R := by
    calc
      _ ≤ (18*N*2^R)*(92*N) := Nat.mul_le_mul hlenbound hrecord
      _ = 1656*N^2*2^R := by ring
  have hscratch : 64*(M6.Transfer.coefficientBits R N +
      M6.Transfer.actualAddressBits R N) ≤ 1728*N^2*2^R := by
    nlinarith [Nat.mul_le_mul_left 1728 hscale]
  have hextra : 4*N ≤ 4*N^2*2^R := by
    nlinarith [Nat.mul_le_mul_left 4 hscale]
  have hbase := M6.Transfer.trace_storage_bound R N hRN
  unfold M6.Transfer.actualTraceStorage
  nlinarith

theorem M6.Transfer.actual_trace_work_bound : ∀ R N : ℕ, R < N → M6.Transfer.actualTraceWork R N ≤ 16384 * N^3 * 4^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.actualTraceWork R N ≤ 16384 * N^3 * 4^R
  intro R N hRN
  classical
  have hN : 1 ≤ N := by omega
  have hslots : 2 * N + 1 ≤ 3 * N := by omega
  have hcharge : M6.Transfer.actualEventBitCharge R N ≤ 616 * N := by
    unfold M6.Transfer.actualEventBitCharge M6.Transfer.coefficientBits M6.Transfer.actualAddressBits
    omega
  have hevents :
      Fintype.card (M6.Transfer.Memory R) * N *
        (M6.Transfer.scatterEventList R N).length =
        6 * N * (2 * N + 1) * 4^R := by
    simpa only [M6.Transfer.traceCoefficientOps, M6.Transfer.scatterEventList,
      Finset.length_toList, Finset.card_univ] using
      M6.Transfer.scatter_loop_count R N
  have hpow : (2^R)^2 = (4 : ℕ)^R := by
    calc
      (2^R)^2 = (2^2)^R := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm R 2]
      _ = 4^R := by norm_num
  have hcount :
      Fintype.card (M6.Transfer.Memory R) * N *
          (M6.Transfer.scatterEventList R N).length +
        (2^R)^2 * N * (2*N+1) ≤ 21 * N^2 * 4^R := by
    rw [hevents, hpow]
    calc
      6 * N * (2*N+1) * 4^R + 4^R * N * (2*N+1) =
          7 * N * (2*N+1) * 4^R := by ring
      _ ≤ 7 * N * (3*N) * 4^R :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (7 * N) hslots)
      _ = 21 * N^2 * 4^R := by ring
  unfold M6.Transfer.actualTraceWork
  calc
    _ ≤ (21 * N^2 * 4^R) * (616 * N) := Nat.mul_le_mul hcount hcharge
    _ = 12936 * (N^3 * 4^R) := by ring
    _ ≤ 16384 * (N^3 * 4^R) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 16384 * N^3 * 4^R := by ring

theorem M6.Transfer.actual_address_capacity : ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N < 2^(M6.Transfer.actualAddressBits R N) := by
  change ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N < 2^(M6.Transfer.actualAddressBits R N)
  intro R N hRN
  have hpow : ∀ n : ℕ, n ≤ 2^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hp : 0 < (2 : ℕ)^n := by positivity
      omega
  have hsq : N^2 ≤ ((2 : ℕ)^N)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (hpow N) (hpow N)
  have heq : (2 : ℕ)^(R + 2*N + 12) = 4096 * (2^N)^2 * 2^R := by
    rw [show R + 2*N + 12 = R + N*2 + 12 by omega]
    simp only [pow_add, pow_mul]
    norm_num
    <;> ring
  calc
    M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R :=
      M6.Transfer.actual_trace_storage_bound R N hRN
    _ ≤ 4096 * (2^N)^2 * 2^R :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4096 hsq)
    _ = 2^(R + 2*N + 12) := heq.symm
    _ < 2^(M6.Transfer.actualAddressBits R N) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
      unfold M6.Transfer.actualAddressBits
      omega

theorem M6.Transfer.indexed_array_correct_resources : ∀ (R N : ℕ) [NeZero N] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ), R < N → (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → (∀ i m t, (W i m t).natDegree ≤ 2) → M6.Transfer.IndexedArrayGuarantee R N W := by
  intro R N inst W hRN hmass hdegree
  classical
  have hsmall (i : ℕ) (hi : i < N) : (8 : ℕ) ^ (i + 1) ≤ 2 ^ R * 8 ^ N := by
    have hexp : i + 1 ≤ N := Nat.succ_le_of_lt hi
    have hpow : 1 ≤ (2 : ℕ) ^ R := Nat.succ_le_of_lt (pow_pos (by decide) R)
    calc
      (8 : ℕ) ^ (i + 1) ≤ 8 ^ N := Nat.pow_le_pow_right (by decide) hexp
      _ = 1 * 8 ^ N := (one_mul _).symm
      _ ≤ 2 ^ R * 8 ^ N := Nat.mul_le_mul_right _ hpow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (M6.Transfer.scalar_trace_polynomial R N W hdegree).trans
      (M6.Transfer.array_trace_inputs R N (Polynomial ℤ) W)
  · exact M6.Transfer.actual_trace_work_bound R N hRN
  · exact M6.Transfer.actual_trace_storage_bound R N hRN
  · exact M6.Transfer.actual_address_capacity R N hRN
  · intro start i hi k addr
    unfold M6.Transfer.FitsSigned
    have h := M6.Transfer.actual_layer_intermediates R N W start i k addr hmass hdegree
    exact lt_of_le_of_lt (le_trans h.1 (hsmall i hi))
      (M6.Transfer.actual_signed_capacity R N)
  · intro start i hi e
    unfold M6.Transfer.FitsSigned
    have h := M6.Transfer.actual_layer_intermediates R N W start i 0
      (start, ⟨0, by omega⟩) hmass hdegree
    exact lt_of_le_of_lt (le_trans (h.2 e) (hsmall i hi))
      (M6.Transfer.actual_signed_capacity R N)
  · intro k d
    unfold M6.Transfer.FitsSigned
    exact lt_of_le_of_lt
      (M6.Transfer.actual_trace_intermediates R N W k d hmass hdegree)
      (M6.Transfer.actual_signed_capacity R N)

theorem M6.ActualTransfer.boundary_indexed_resources : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.span a b < N → M6.Transfer.IndexedArrayGuarantee (M6.ActualTransfer.span a b) N (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P) := by
  intro N inst a b P h
  refine M6.Transfer.indexed_array_correct_resources
    (M6.ActualTransfer.span a b) N
    (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P)
    h ?_ ?_
  · intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).1
  · intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).2

theorem M6.ActualTransfer.character_indexed_resources : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.span a b < N → M6.Transfer.IndexedArrayGuarantee (M6.ActualTransfer.span a b) N (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P) := by
  intro N inst a b P h
  refine M6.Transfer.indexed_array_correct_resources (M6.ActualTransfer.span a b) N (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P) h ?_ ?_
  · intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).1
  · intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).2

theorem M6.Transfer.paired_storage_bound : ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryStorage R N ≤ 8192*N^2*2^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryStorage R N ≤ 8192 * N^2 * 2^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := by omega
  have hp : 1 ≤ 2^R := Nat.one_le_pow R 2 (by omega)
  have hNN : N ≤ N^2 := by nlinarith
  have hRP : R * 2^R ≤ N * 2^R := Nat.mul_le_mul_right _ hR
  have hNP : N * 2^R ≤ N^2 * 2^R := Nat.mul_le_mul_right _ hNN
  have hP : 2^R ≤ N * 2^R := by nlinarith
  have hN2P : N^2 ≤ N^2 * 2^R := by nlinarith
  have hRNP : R * N * 2^R ≤ N^2 * 2^R := by
    calc
      R * N * 2^R ≤ N * N * 2^R := by gcongr
      _ = N^2 * 2^R := by ring
  have hs := M6.Transfer.actual_trace_storage_bound R N hRN
  simp only [M6.Transfer.pairedQueryStorage, M6.Transfer.queryCoefficientBits,
    M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
    M6.Transfer.PostEvent, Fintype.card_prod, Fintype.card_fin]
  first
  | nlinarith
  | simp only [M6.Transfer.actualTraceStorage, M6.Transfer.traceStorageModel,
      M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
      M6.Transfer.addressBits, M6.Transfer.CoefficientAddress,
      Fintype.card_prod, Fintype.card_fin, M6.Transfer.state_count]
    nlinarith

theorem M6.Transfer.paired_work_bound : ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryWork R N ≤ 40000*N^3*4^R := by
  change ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryWork R N ≤ 40000 * N^3 * 4^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := Nat.le_of_lt hRN
  have h4 : 1 ≤ (4 : ℕ)^R := Nat.one_le_pow _ _ (by omega)
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN2]
  have hRN1 : R * N ≤ N^2 := by nlinarith [Nat.mul_le_mul_right N hR]
  have hRN2 : R * N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_right (N^2) hR]
  have hscale : N^3 ≤ N^3 * 4^R := by simpa using Nat.mul_le_mul_left (N^3) h4
  have hw := M6.Transfer.actual_trace_work_bound R N hRN
  have hp : M6.Transfer.postWork R N ≤ 7232 * N^3 * 4^R := by
    simp [M6.Transfer.postWork, M6.Transfer.PostEvent,
      M6.Transfer.queryCoefficientBits, M6.Transfer.coefficientBits,
      M6.Transfer.actualAddressBits, M6.Transfer.addressBits]
    <;> nlinarith
  unfold M6.Transfer.pairedQueryWork
  nlinarith

theorem M6.Transfer.post_event_count : ∀ N : ℕ, Fintype.card (M6.Transfer.PostEvent N) = 4*(2*N+1) := by
  change ∀ N : ℕ, Fintype.card (M6.Transfer.PostEvent N) = 4 * (2 * N + 1)
  intro N
  simp [M6.Transfer.PostEvent, M6.Transfer.Bit, Fintype.card_prod] <;> ring

theorem M6.Transfer.distance_work_bound : ∀ R N e : ℕ, R < N → e ≤ 180*(N+1)^3 → M6.Transfer.distanceWork R N e ≤ 50000*N^3*4^R := by
  change ∀ R N e : ℕ, R < N → e ≤ 180 * (N + 1)^3 → M6.Transfer.distanceWork R N e ≤ 50000 * N^3 * 4^R
  intro R N e hRN he
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := Nat.le_of_lt hRN
  have h4 : 1 ≤ (4 : ℕ)^R := Nat.one_le_pow _ _ (by omega)
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN2]
  have hRN1 : R * N ≤ N^2 := by nlinarith [Nat.mul_le_mul_right N hR]
  have hRN2 : R * N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_right (N^2) hR]
  have hcube : (N + 1)^3 ≤ 8 * N^3 := by nlinarith
  have he' : e ≤ 1440 * N^3 := by omega
  have hscale : N^3 ≤ N^3 * 4^R := by simpa using Nat.mul_le_mul_left (N^3) h4
  have hp := M6.Transfer.paired_work_bound R N hRN
  simp [M6.Transfer.distanceWork, M6.Transfer.pinMaintenanceWork,
    M6.Transfer.PostEvent, M6.Transfer.queryCoefficientBits,
    M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
    M6.Transfer.addressBits]
  <;> nlinarith

theorem M6.Transfer.solve_storage_bound : ∀ R N slots : ℕ, R < N → slots ≤ 512*(N+1)^2 → M6.Transfer.solveStorage R N slots ≤ 16384*N^2*2^R := by
  change ∀ R N slots : ℕ, R < N → slots ≤ 512 * (N + 1)^2 → M6.Transfer.solveStorage R N slots ≤ 16384 * N^2 * 2^R
  intro R N slots hRN hslots
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := by omega
  have hp : 1 ≤ 2^R := Nat.one_le_pow R 2 (by omega)
  have hNN : N ≤ N^2 := by nlinarith
  have hN2P : N^2 ≤ N^2 * 2^R := by nlinarith
  have hNP : N * 2^R ≤ N^2 * 2^R := Nat.mul_le_mul_right _ hNN
  have hRP : R * 2^R ≤ N * 2^R := Nat.mul_le_mul_right _ hR
  have hP : 2^R ≤ N * 2^R := by nlinarith
  have hslots' : slots ≤ 2048 * (N^2 * 2^R) := by nlinarith
  have hs := M6.Transfer.paired_storage_bound R N hRN
  simp only [M6.Transfer.solveStorage, M6.Transfer.queryCoefficientBits,
    M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
    M6.Transfer.PostEvent, Fintype.card_prod, Fintype.card_fin]
  nlinarith

theorem M6.Transfer.witness_work_bound : ∀ R N e k : ℕ, R < N → e ≤ 180*(N+1)^3 → k ≤ 2*N → M6.Transfer.witnessWork R N e k ≤ 200000*N^4*4^R := by
  change ∀ R N e k : ℕ, R < N → e ≤ 180 * (N + 1)^3 → k ≤ 2 * N → M6.Transfer.witnessWork R N e k ≤ 200000 * N^4 * 4^R
  intro R N e k hRN he hk
  have hN : 1 ≤ N := by omega
  have hR : R ≤ N := Nat.le_of_lt hRN
  have h4 : 1 ≤ (4 : ℕ)^R := Nat.one_le_pow _ _ (by omega)
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN2]
  have hN4 : N^3 ≤ N^4 := by nlinarith [Nat.mul_le_mul_left N hN3]
  have he' : e ≤ 1440 * N^3 := by
    nlinarith [show (N + 1)^3 ≤ (2 * N)^3 from Nat.pow_le_pow_left (by omega) 3]
  have heN : e * N ≤ 1440 * N^4 := by
    nlinarith [Nat.mul_le_mul_right N he']
  have heR : e * R ≤ 1440 * N^4 := by
    nlinarith [Nat.mul_le_mul_left e hR]
  have hkN : k * N ≤ 2 * N^2 := by
    nlinarith [Nat.mul_le_mul_right N hk]
  have hkN2 : k * N^2 ≤ 2 * N^3 := by
    nlinarith [Nat.mul_le_mul_right (N^2) hk]
  have hkR : k * R ≤ 2 * N^2 := by
    nlinarith [Nat.mul_le_mul_left k hR]
  have hkRN : k * R * N ≤ 2 * N^3 := by
    nlinarith [Nat.mul_le_mul_right N hkR]
  have hRN' : R * N ≤ N^2 := by
    nlinarith [Nat.mul_le_mul_right N hR]
  have hs3 : N^3 ≤ N^4 * 4^R := by
    nlinarith [Nat.mul_le_mul_left (N^4) h4]
  have hs4 : N^4 ≤ N^4 * 4^R := by
    simpa using Nat.mul_le_mul_left (N^4) h4
  have hp := M6.Transfer.paired_work_bound R N hRN
  have hpN : N * M6.Transfer.pairedQueryWork R N ≤ 40000 * N^4 * 4^R := by
    nlinarith [Nat.mul_le_mul_left N hp]
  have hpk : k * M6.Transfer.pairedQueryWork R N ≤ 80000 * N^4 * 4^R := by
    nlinarith [Nat.mul_le_mul_right (M6.Transfer.pairedQueryWork R N) hk]
  have hp' : M6.Transfer.pairedQueryWork R N ≤ 40000 * N^4 * 4^R := by
    nlinarith [Nat.mul_le_mul_right (M6.Transfer.pairedQueryWork R N) hN]
  simp [M6.Transfer.witnessWork, M6.Transfer.distanceWork,
    M6.Transfer.pinMaintenanceWork, M6.Transfer.queryCoefficientBits,
    M6.Transfer.coefficientBits, M6.Transfer.actualAddressBits,
    M6.Transfer.addressBits]
  <;> nlinarith

theorem M6.ActualTransfer.scalar_trace_support : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), 2*N < d → (M6.Transfer.scalarTracePolynomial W N).coeff d = 0 := by
  intro R N W d hd
  classical
  unfold M6.Transfer.scalarTracePolynomial
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : (i : ℕ) ≠ d := by
    have hi_lt := i.isLt
    omega
  simp [Polynomial.coeff_monomial, hne]

theorem M6.ActualTransfer.shift_division : ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2:ℤ)^k := by
  intro z k
  simpa only [Int.shiftRight_eq, Nat.cast_pow, Nat.cast_ofNat] using Int.shiftRight_eq_div_pow z k

theorem M6.ActualTransfer.shifted_coefficient_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), M6.ActualTransfer.shiftedCoefficient N a b P d = (M6.ActualTransfer.Q N a b P).coeff d := by
  intro N inst a b P d
  simp [M6.ActualTransfer.shiftedCoefficient, M6.ActualTransfer.Q,
    Polynomial.coeff_sub, M6.Normalize.divide_coeff,
    M6.ActualTransfer.shift_division]

theorem M6.ActualTransfer.shifted_output_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.shiftedOutput N a b P = M6.ActualTransfer.Q N a b P := by
  intro N inst a b P
  classical
  have hsupport : ∀ d, 2 * N < d → (M6.ActualTransfer.Q N a b P).coeff d = 0 := by
    intro d hd
    simp only [M6.ActualTransfer.Q, Polynomial.coeff_sub,
      M6.Normalize.divide_coeff, M6.ActualTransfer.boundaryTrace,
      M6.ActualTransfer.characterTrace]
    rw [M6.ActualTransfer.scalar_trace_support _ N _ d hd,
      M6.ActualTransfer.scalar_trace_support _ N _ d hd]
    simp
  apply Polynomial.ext
  intro d
  unfold M6.ActualTransfer.shiftedOutput
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    M6.ActualTransfer.shifted_coefficient_exact]
  by_cases hd : d < 2 * N + 1
  · rw [Finset.sum_eq_single (⟨d, hd⟩ : Fin (2 * N + 1))]
    · simp
    · intro i hi hne
      have hval : (i : ℕ) ≠ d := by
        intro h
        apply hne
        exact Fin.ext h
      simp [hval]
    · simp
  · rw [hsupport d (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    have hval : (i : ℕ) ≠ d := by
      have hi_lt := i.isLt
      omega
    simp [hval]

theorem M6.ActualTransfer.shifted_scan_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.shiftedScan N a b P = M6.Pinned.firstPositive (2*N) (M6.ActualTransfer.Q N a b P) := by
  intro N inst a b P
  classical
  simp only [M6.ActualTransfer.shiftedScan, M6.Pinned.firstPositive,
    M6.ActualTransfer.shifted_coefficient_exact]

theorem M6.Transfer.division_difference_fits : ∀ (R N : ℕ) (z w : ℤ) (j k : ℕ), z.natAbs ≤ 2^R*8^N → w.natAbs ≤ 2^R*8^N → (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs < 2^(M6.Transfer.queryCoefficientBits R N - 1) := by
  change ∀ (R N : ℕ) (z w : ℤ) (j k : ℕ), z.natAbs ≤ 2^R*8^N → w.natAbs ≤ 2^R*8^N → (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs < 2^(M6.Transfer.queryCoefficientBits R N - 1)
  intro R N z w j k hz hw
  have hz' := Int.natAbs_ediv_le_natAbs z ((2 : ℤ)^j)
  have hw' := Int.natAbs_ediv_le_natAbs w ((2 : ℤ)^k)
  have htri : (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs ≤
      (z/(2:ℤ)^j).natAbs + (w/(2:ℤ)^k).natAbs := by
    simpa only [sub_eq_add_neg, Int.natAbs_neg] using
      (Int.natAbs_add_le (z/(2:ℤ)^j) (-(w/(2:ℤ)^k)))
  have hbound : (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs ≤ 2 * (2^R*8^N) := by
    omega
  have hcap := M6.Transfer.actual_signed_capacity R N
  have hdouble : 2 * (2^R*8^N) < 2^((M6.Transfer.coefficientBits R N - 1) + 1) := by
    rw [pow_succ]
    omega
  have hexp : (M6.Transfer.coefficientBits R N - 1) + 1 ≤
      M6.Transfer.queryCoefficientBits R N - 1 := by
    unfold M6.Transfer.queryCoefficientBits
    omega
  have hpow : (2 : ℕ)^((M6.Transfer.coefficientBits R N - 1) + 1) ≤
      2^(M6.Transfer.queryCoefficientBits R N - 1) :=
    Nat.pow_le_pow_right (by decide) hexp
  exact lt_of_le_of_lt hbound (lt_of_lt_of_le hdouble hpow)

theorem M6.ActualTransfer.query_coefficients_fit : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), ((M6.ActualTransfer.Q N a b P).coeff d).natAbs < 2^(M6.Transfer.queryCoefficientBits (M6.ActualTransfer.span a b) N - 1) := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), ((M6.ActualTransfer.Q N a b P).coeff d).natAbs < 2^(M6.Transfer.queryCoefficientBits (M6.ActualTransfer.span a b) N - 1)
  intro N inst a b P d
  have hb : ((M6.ActualTransfer.boundaryTrace N a b P).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N := by
    have hdeg : ∀ i m t, (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
      intro i m t
      exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).2
    unfold M6.ActualTransfer.boundaryTrace
    rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg]
    apply M6.Transfer.trace_coefficient_bound
    intro i m t
    exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).1
  have hc : ((M6.ActualTransfer.characterTrace N a b P).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N := by
    have hdeg : ∀ i m t, (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
      intro i m t
      exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).2
    unfold M6.ActualTransfer.characterTrace
    rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg]
    apply M6.Transfer.trace_coefficient_bound
    intro i m t
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).1
  unfold M6.ActualTransfer.Q
  simp only [Polynomial.coeff_sub, M6.Normalize.divide_coeff]
  apply M6.Transfer.division_difference_fits <;> assumption

theorem M6.Euclid.binary_normalization : ∀ p : M6.Euclid.BP, (p ≠ 0 → p.Monic) ∧ normalize p = p := by
  change ∀ p : M6.Euclid.BP, (p ≠ 0 → p.Monic) ∧ normalize p = p
  intro p
  have hm : p ≠ 0 → p.Monic := by
    intro hp
    change p.leadingCoeff = 1
    have binary : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases binary p.leadingCoeff with h | h
    · exact False.elim (hp (Polynomial.leadingCoeff_eq_zero.mp h))
    · exact h
  refine ⟨hm, ?_⟩
  by_cases hp : p = 0
  · subst p
    simp
  · exact (hm hp).normalize_eq_self

theorem M6.Euclid.cancel_mod : ∀ p q : M6.Euclid.BP, M6.Euclid.cancel p q % q = p % q := by
  change ∀ p q : M6.Euclid.BP, M6.Euclid.cancel p q % q = p % q
  intro p q
  apply Polynomial.mod_eq_of_dvd_sub
  simp [M6.Euclid.cancel, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem M6.Euclid.dense_injective : ∀ (N : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ N + 1 → M6.Euclid.rank q ≤ N + 1 → M6.Euclid.dense N p = M6.Euclid.dense N q → p = q := by
  change ∀ (N : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ N + 1 → M6.Euclid.rank q ≤ N + 1 → M6.Euclid.dense N p = M6.Euclid.dense N q → p = q
  intro N p q hp hq hd
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < N + 1
  · change List.ofFn (fun j : Fin (N + 1) => p.coeff j) = List.ofFn (fun j : Fin (N + 1) => q.coeff j) at hd
    have he : (List.ofFn (fun j : Fin (N + 1) => p.coeff j))[i]'(by simpa using hi) = (List.ofFn (fun j : Fin (N + 1) => q.coeff j))[i]'(by simpa using hi) := by
      congr 1
    simpa only [List.getElem_ofFn] using he
  · have hpz : p.coeff i = 0 := by
      by_cases hp0 : p = 0
      · simp [hp0]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simp [M6.Euclid.rank, hp0] at hp
        omega
    have hqz : q.coeff i = 0 := by
      by_cases hq0 : q = 0
      · simp [hq0]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simp [M6.Euclid.rank, hq0] at hq
        omega
    exact hpz.trans hqz.symm

theorem M6.Euclid.dense_rank : ∀ (width : ℕ) (p : M6.Euclid.BP), M6.Euclid.rank p ≤ width → M6.Euclid.scanRank width p = M6.Euclid.rank p := by
  change ∀ (width : ℕ) (p : M6.Euclid.BP), M6.Euclid.rank p ≤ width → M6.Euclid.scanRank width p = M6.Euclid.rank p
  classical
  intro width
  induction width with
  | zero =>
      intro p h
      have hr : M6.Euclid.rank p = 0 := Nat.eq_zero_of_le_zero h
      simpa [M6.Euclid.scanRank] using hr.symm
  | succ width ih =>
      intro p h
      by_cases hlow : M6.Euclid.rank p ≤ width
      · have hc : p.coeff width = 0 := by
          by_cases hp : p = 0
          · simp [hp]
          · have hd : p.natDegree < width := by
              simp [M6.Euclid.rank, hp] at hlow
              omega
            exact Polynomial.coeff_eq_zero_of_natDegree_lt hd
        simpa [M6.Euclid.scanRank, List.range_succ, List.foldl_append, hc] using ih p hlow
      · have hr : M6.Euclid.rank p = width + 1 := by omega
        have hp : p ≠ 0 := by
          intro hp
          simp [M6.Euclid.rank, hp] at hlow
        have hd : p.natDegree = width := by
          simp [M6.Euclid.rank, hp] at hr
          omega
        have hc : p.coeff width ≠ 0 := by
          rw [← hd, Polynomial.coeff_natDegree]
          intro hz
          exact hp (Polynomial.leadingCoeff_eq_zero.mp hz)
        simpa [M6.Euclid.scanRank, List.range_succ, List.foldl_append, hc] using hr.symm

theorem M6.Euclid.rank_order : ∀ p q : M6.Euclid.BP, (M6.Euclid.rank p < M6.Euclid.rank q ↔ p.degree < q.degree) ∧ (M6.Euclid.rank p ≤ M6.Euclid.rank q ↔ p.degree ≤ q.degree) := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.rank p < M6.Euclid.rank q ↔ p.degree < q.degree) ∧ (M6.Euclid.rank p ≤ M6.Euclid.rank q ↔ p.degree ≤ q.degree)
  intro p q
  by_cases hp : p = 0 <;> by_cases hq : q = 0
  · subst p
    subst q
    simp [M6.Euclid.rank]
  · subst p
    simp [M6.Euclid.rank, hq, Polynomial.degree_eq_natDegree hq]
  · subst q
    simp [M6.Euclid.rank, hp, Polynomial.degree_eq_natDegree hp]
  · simp [M6.Euclid.rank, hp, hq, Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq]

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

theorem M6.Euclid.scan_cost : ∀ width : ℕ, M6.Euclid.scanCost width = width * (6 * width + 4) ∧ (0 < width → M6.Euclid.scanCost width ≤ 10 * width ^ 2) := by
  change ∀ width : ℕ, M6.Euclid.scanCost width = width * (6 * width + 4) ∧ (0 < width → M6.Euclid.scanCost width ≤ 10 * width ^ 2)
  intro width
  have hloop (l : List ℕ) (a : ℕ) :
      l.foldl (fun acc _ => acc + (6 * width + 4)) a =
        a + l.length * (6 * width + 4) := by
    induction l generalizing a with
    | nil => simp
    | cons i l ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        ring
  have hcost : M6.Euclid.scanCost width = width * (6 * width + 4) := by
    simpa [M6.Euclid.scanCost, Nat.add_assoc] using hloop (List.range width) 0
  refine ⟨hcost, ?_⟩
  intro hw
  rw [hcost]
  have hw1 : 1 ≤ width := hw
  have hsq := Nat.mul_le_mul_left width hw1
  nlinarith

theorem M6.Euclid.cancel_drop : ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p := by
  change ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p
  intro p q hp hq hdeg
  apply ((M6.Euclid.rank_order (M6.Euclid.cancel p q) p).1).mpr
  have hmp := (M6.Euclid.binary_normalization p).1 hp
  have hmq := (M6.Euclid.binary_normalization q).1 hq
  simpa [M6.Euclid.cancel, hmp.leadingCoeff, mul_comm, mul_left_comm, mul_assoc] using
    (Polynomial.div_wf_lemma (p := p) (q := q) ⟨hdeg, hp⟩ hmq)

theorem M6.Euclid.dense_cancel : ∀ (N : ℕ) (p q : M6.Euclid.BP), p ≠ 0 → M6.Euclid.dense N (M6.Euclid.cancel p q) = M6.Euclid.denseXor N p q (p.natDegree - q.natDegree) := by
  change ∀ (N : ℕ) (p q : M6.Euclid.BP), p ≠ 0 → _
  intro N p q hp
  have hl : p.leadingCoeff = 1 := (M6.Euclid.binary_normalization p).1 hp
  have hsub : ∀ a b : ZMod 2, a - b = a + b := by decide
  have hc : M6.Euclid.cancel p q = p - q * Polynomial.X ^ (p.natDegree - q.natDegree) := by
    simp [M6.Euclid.cancel, hl, mul_comm, mul_left_comm, mul_assoc]
  rw [hc]
  unfold M6.Euclid.dense M6.Euclid.denseXor
  congr 1
  funext i
  simp [Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', hsub]

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

theorem M6.Euclid.normalized_gcd : ∀ p q : M6.Euclid.BP, EuclideanDomain.gcd q p = GCDMonoid.gcd p q := by
  change ∀ p q : M6.Euclid.BP, EuclideanDomain.gcd q p = GCDMonoid.gcd p q
  intro p q
  apply dvd_antisymm_of_normalize_eq
    (M6.Euclid.binary_normalization (EuclideanDomain.gcd q p)).2
    (M6.Euclid.binary_normalization (GCDMonoid.gcd p q)).2
  · exact GCDMonoid.dvd_gcd
      (EuclideanDomain.gcd_dvd_right q p)
      (EuclideanDomain.gcd_dvd_left q p)
  · exact EuclideanDomain.dvd_gcd
      (GCDMonoid.gcd_dvd_right p q)
      (GCDMonoid.gcd_dvd_left p q)

theorem M6.Euclid.euclid_passes : ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).passes = 2 * (M6.Euclid.euclid p q).cancellations + 3 * (M6.Euclid.euclid p q).rounds + 2 := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).passes = 2 * (M6.Euclid.euclid p q).cancellations + 3 * (M6.Euclid.euclid p q).rounds + 2
  intro p q
  simp [M6.Euclid.euclid, M6.Euclid.euclid_aux_passes] <;> omega

theorem M6.Euclid.remainder_aux_correct : ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ fuel → (M6.Euclid.remainderAux fuel p q).value = p % q ∧ (M6.Euclid.remainderAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.remainderAux fuel p q).value ≤ M6.Euclid.rank p := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ fuel → (M6.Euclid.remainderAux fuel p q).value = p % q ∧ (M6.Euclid.remainderAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.remainderAux fuel p q).value ≤ M6.Euclid.rank p
  intro fuel
  induction fuel with
  | zero =>
      intro p q hf
      have hp : p = 0 := by
        by_contra hp
        simp [M6.Euclid.rank, hp] at hf
      subst p
      simp [M6.Euclid.remainderAux, M6.Euclid.rank]
  | succ fuel ih =>
      intro p q hf
      by_cases hp : p = 0
      · subst p
        simp [M6.Euclid.remainderAux, M6.Euclid.rank]
      by_cases hq : q = 0
      · subst q
        simp [M6.Euclid.remainderAux]
      by_cases hd : p.degree < q.degree
      · have hm : p % q = p := (Polynomial.mod_eq_self_iff hq).2 hd
        simp [M6.Euclid.remainderAux, hp, hq, hd, hm]
      · have hle : q.degree ≤ p.degree := le_of_not_gt hd
        have hdrop := M6.Euclid.cancel_drop p q hp hq hle
        have hbudget : M6.Euclid.rank (M6.Euclid.cancel p q) ≤ fuel := by omega
        obtain ⟨hvalue, hcost⟩ := ih (M6.Euclid.cancel p q) q hbudget
        have hv : (M6.Euclid.remainderAux fuel (M6.Euclid.cancel p q) q).value = p % q :=
          hvalue.trans (M6.Euclid.cancel_mod p q)
        have hc : (M6.Euclid.remainderAux fuel (M6.Euclid.cancel p q) q).cancellations + 1 + M6.Euclid.rank (M6.Euclid.remainderAux fuel (M6.Euclid.cancel p q) q).value ≤ M6.Euclid.rank p := by
          omega
        simpa [M6.Euclid.remainderAux, hp, hq, hd, hle, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro hv hc

theorem M6.Euclid.remainder_safe : ∀ (fuel : ℕ) (p q : M6.Euclid.BP) (width : ℕ), M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.remainderSafe fuel p q width := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP) (width : ℕ), M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.remainderSafe fuel p q width
  intro fuel
  induction fuel with
  | zero =>
      intro p q width hp hq
      simp [M6.Euclid.remainderSafe, hp, hq]
  | succ fuel ih =>
      intro p q width hp hq
      by_cases hp0 : p = 0
      · subst p
        simp [M6.Euclid.remainderSafe, hp, hq]
      by_cases hq0 : q = 0
      · subst q
        simp [M6.Euclid.remainderSafe, hp, hq]
      by_cases hdeg : p.degree < q.degree
      · simp [M6.Euclid.remainderSafe, hp0, hq0, hdeg, hp, hq]
      · have hc : M6.Euclid.rank (M6.Euclid.cancel p q) ≤ width :=
          le_trans (Nat.le_of_lt (M6.Euclid.cancel_drop p q hp0 hq0 (le_of_not_gt hdeg))) hp
        have hs := ih (M6.Euclid.cancel p q) q width hc hq
        simp [M6.Euclid.remainderSafe, hp0, hq0, hdeg, hp, hq, hs]

theorem M6.Euclid.remainder_correct : ∀ p q : M6.Euclid.BP, (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p ∧ (q ≠ 0 → M6.Euclid.rank (M6.Euclid.remainder p q).value < M6.Euclid.rank q) := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p ∧ (q ≠ 0 → M6.Euclid.rank (M6.Euclid.remainder p q).value < M6.Euclid.rank q)
  intro p q
  have h : (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p := by
    simpa [M6.Euclid.remainder] using
      (M6.Euclid.remainder_aux_correct (M6.Euclid.rank p) p q (le_refl _))
  refine ⟨h.1, h.2, ?_⟩
  intro hq
  rw [h.1]
  apply ((M6.Euclid.rank_order (p % q) q).1).mpr
  exact Polynomial.degree_mod_lt p hq

theorem M6.Euclid.euclid_aux_correct : ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank q < fuel → (M6.Euclid.euclidAux fuel p q).value = EuclideanDomain.gcd q p ∧ (M6.Euclid.euclidAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclidAux fuel p q).rounds ≤ M6.Euclid.rank q := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank q < fuel → (M6.Euclid.euclidAux fuel p q).value = EuclideanDomain.gcd q p ∧ (M6.Euclid.euclidAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclidAux fuel p q).rounds ≤ M6.Euclid.rank q
  intro fuel
  induction fuel with
  | zero =>
      intro p q hf
      omega
  | succ fuel ih =>
      intro p q hf
      by_cases hq : q = 0
      · subst q
        simp [M6.Euclid.euclidAux, M6.Euclid.rank, EuclideanDomain.gcd_zero_left, (M6.Euclid.binary_normalization p).2]
      · obtain ⟨hrvalue, hrcost, hrdrop⟩ := M6.Euclid.remainder_correct p q
        have hdrop := hrdrop hq
        have hbudget : M6.Euclid.rank (M6.Euclid.remainder p q).value < fuel := by omega
        obtain ⟨hvalue, hcost, hrounds⟩ := ih q (M6.Euclid.remainder p q).value hbudget
        have hv : (M6.Euclid.euclidAux fuel q (M6.Euclid.remainder p q).value).value = EuclideanDomain.gcd q p := by
          calc
            _ = EuclideanDomain.gcd (M6.Euclid.remainder p q).value q := hvalue
            _ = EuclideanDomain.gcd (p % q) q := by rw [hrvalue]
            _ = EuclideanDomain.gcd q p := (EuclideanDomain.gcd_val q p).symm
        simp only [M6.Euclid.euclidAux, hq, ↓reduceIte]
        refine ⟨hv, ?_, ?_⟩ <;> omega

theorem M6.Euclid.euclid_output_width : ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ max (M6.Euclid.rank p) (M6.Euclid.rank q) := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ max (M6.Euclid.rank p) (M6.Euclid.rank q)
  intro fuel
  induction fuel with
  | zero =>
      intro p q
      simpa [M6.Euclid.euclidAux] using (le_max_left (M6.Euclid.rank p) (M6.Euclid.rank q))
  | succ fuel ih =>
      intro p q
      by_cases hq : q = 0
      · simpa [M6.Euclid.euclidAux, hq] using (le_max_left (M6.Euclid.rank p) (M6.Euclid.rank q))
      · have hr := (M6.Euclid.remainder_correct p q).2.1
        have hi := ih q (M6.Euclid.remainder p q).value
        have hb : M6.Euclid.rank (M6.Euclid.euclidAux fuel q (M6.Euclid.remainder p q).value).value ≤ max (M6.Euclid.rank p) (M6.Euclid.rank q) := by
          omega
        simpa [M6.Euclid.euclidAux, hq] using hb

theorem M6.Euclid.euclid_safe : ∀ (fuel : ℕ) (p q : M6.Euclid.BP) (width : ℕ), M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.euclidSafe fuel p q width := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP) (width : ℕ), M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.euclidSafe fuel p q width
  intro fuel
  induction fuel with
  | zero =>
      intro p q width hp hq
      simp [M6.Euclid.euclidSafe, hp, hq]
  | succ fuel ih =>
      intro p q width hp hq
      by_cases hq0 : q = 0
      · subst q
        simp [M6.Euclid.euclidSafe, hp, hq]
      · have hr : M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ width := by
          have hc := (M6.Euclid.remainder_correct p q).2.1
          omega
        have hs : ∀ n, M6.Euclid.remainderSafe n p q width :=
          fun n => M6.Euclid.remainder_safe n p q width hp hq
        have ht := ih q (M6.Euclid.remainder p q).value width hq hr
        simp [M6.Euclid.euclidSafe, hq0, hp, hq, hs, ht]

theorem M6.Euclid.euclid_correct : ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).value = GCDMonoid.gcd p q ∧ (M6.Euclid.euclid p q).cancellations ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclid p q).rounds ≤ M6.Euclid.rank q := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).value = GCDMonoid.gcd p q ∧ (M6.Euclid.euclid p q).cancellations ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclid p q).rounds ≤ M6.Euclid.rank q
  intro p q
  obtain ⟨hv, hc, hr⟩ := M6.Euclid.euclid_aux_correct (M6.Euclid.rank q + 1) p q (by omega)
  have hv' := hv.trans (M6.Euclid.normalized_gcd p q)
  have hc' : (M6.Euclid.euclidAux (M6.Euclid.rank q + 1) p q).cancellations ≤ M6.Euclid.rank p + M6.Euclid.rank q := by
    omega
  simpa only [M6.Euclid.euclid] using And.intro hv' (And.intro hc' hr)

theorem M6.Euclid.bit_cost_bound : ∀ (N : ℕ) (p q : M6.Euclid.BP), p.natDegree ≤ N → q.natDegree ≤ N → M6.Euclid.bitCost N p q ≤ 90 * (N + 1) ^ 3 ∧ M6.Euclid.euclidSafe (M6.Euclid.rank q + 1) p q (N + 1) := by
  change ∀ (N : ℕ) (p q : M6.Euclid.BP), p.natDegree ≤ N → q.natDegree ≤ N → M6.Euclid.bitCost N p q ≤ 90 * (N + 1) ^ 3 ∧ M6.Euclid.euclidSafe (M6.Euclid.rank q + 1) p q (N + 1)
  intro N p q hp hq
  have hrp : M6.Euclid.rank p ≤ N + 1 := by
    by_cases h : p = 0
    · simp [M6.Euclid.rank, h]
    · simp only [M6.Euclid.rank, h, ↓reduceIte]
      omega
  have hrq : M6.Euclid.rank q ≤ N + 1 := by
    by_cases h : q = 0
    · simp [M6.Euclid.rank, h]
    · simp only [M6.Euclid.rank, h, ↓reduceIte]
      omega
  refine ⟨?_, M6.Euclid.euclid_safe _ p q (N + 1) hrp hrq⟩
  obtain ⟨_, hc, he⟩ := M6.Euclid.euclid_correct p q
  have hpasses := M6.Euclid.euclid_passes p q
  have hb : (M6.Euclid.euclid p q).passes ≤ 9 * (N + 1) := by omega
  have hs : M6.Euclid.scanCost (N + 1) ≤ 10 * (N + 1) ^ 2 :=
    (M6.Euclid.scan_cost (N + 1)).2 (by omega)
  have hmul := Nat.mul_le_mul hb hs
  have hbound : (M6.Euclid.euclid p q).passes * M6.Euclid.scanCost (N + 1) ≤ 90 * (N + 1) ^ 3 := by
    calc
      _ ≤ (9 * (N + 1)) * (10 * (N + 1) ^ 2) := hmul
      _ = 90 * (N + 1) ^ 3 := by ring
  simpa only [M6.Euclid.bitCost, Nat.mul_comm] using hbound

theorem M6.Euclid.preprocess_correct_cost : ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → (M6.Euclid.preprocess a b M).value = GCDMonoid.gcd (GCDMonoid.gcd a b) M ∧ M6.Euclid.preprocessBitCost N a b M ≤ 180 * (N + 1) ^ 3 := by
  change ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → (M6.Euclid.preprocess a b M).value = GCDMonoid.gcd (GCDMonoid.gcd a b) M ∧ M6.Euclid.preprocessBitCost N a b M ≤ 180 * (N + 1) ^ 3
  intro N a b M ha hb hM
  have hrank (p : M6.Euclid.BP) (hp : p.natDegree ≤ N) : M6.Euclid.rank p ≤ N + 1 := by
    by_cases h : p = 0
    · simp [M6.Euclid.rank, h]
    · simp only [M6.Euclid.rank, h, ↓reduceIte]
      omega
  have hw : M6.Euclid.rank (M6.Euclid.euclid a b).value ≤ max (M6.Euclid.rank a) (M6.Euclid.rank b) := by
    simpa only [M6.Euclid.euclid] using M6.Euclid.euclid_output_width (M6.Euclid.rank b + 1) a b
  have hw' : M6.Euclid.rank (M6.Euclid.euclid a b).value ≤ N + 1 :=
    hw.trans (max_le (hrank a ha) (hrank b hb))
  have hd : (M6.Euclid.euclid a b).value.natDegree ≤ N := by
    by_cases h : (M6.Euclid.euclid a b).value = 0
    · simp [h]
    · simp only [M6.Euclid.rank, h, ↓reduceIte] at hw'
      omega
  constructor
  · change (M6.Euclid.euclid (M6.Euclid.euclid a b).value M).value = GCDMonoid.gcd (GCDMonoid.gcd a b) M
    rw [(M6.Euclid.euclid_correct a b).1]
    exact (M6.Euclid.euclid_correct (GCDMonoid.gcd a b) M).1
  · have h₁ := (M6.Euclid.bit_cost_bound N a b ha hb).1
    have h₂ := (M6.Euclid.bit_cost_bound N (M6.Euclid.euclid a b).value M hd hM).1
    have heq : M6.Euclid.preprocessBitCost N a b M = M6.Euclid.bitCost N a b + M6.Euclid.bitCost N (M6.Euclid.euclid a b).value M := by
      simp only [M6.Euclid.preprocessBitCost, M6.Euclid.preprocess, M6.Euclid.bitCost]
      ring
    rw [heq]
    omega

theorem M6.ActualTransfer.actual_solve_queries : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) → k ≤ 2*N := by
  intro N inst a b d v k h
  have hbound : ∀ c : M6.Pinned.Pins (2*N) → ℤ,
      (M6.Pinned.recover c (M6.Pinned.free (2*N)) (List.finRange (2*N))).2 ≤ 2*N := by
    intro c
    simpa using (M6.Pinned.recover_properties (2*N) c
      (M6.Pinned.free (2*N)) (List.finRange (2*N))).2.2
  unfold M6.ActualTransfer.solve M6.Pinned.solve at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨hd, hv, hk⟩
    rw [← hk]
    exact hbound _

theorem M6.ActualTransfer.actual_distance_work : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → M6.ActualTransfer.actualDistanceWork N a b ≤ 50000*N^3*4^(M6.ActualTransfer.span a b) := by
  intro N inst a b hspan
  have ha : a.natDegree ≤ N := by
    have h := (max_le_iff.mp (Nat.le_of_lt hspan : M6.ActualTransfer.span a b ≤ N)).1
    exact h
  have hb : b.natDegree ≤ N := by
    have h := (max_le_iff.mp (Nat.le_of_lt hspan : M6.ActualTransfer.span a b ≤ N)).2
    exact h
  have hM : (M6.Cyclic.modulus N).natDegree ≤ N := by
    change (Polynomial.X ^ N + (1 : Polynomial (ZMod 2))).natDegree ≤ N
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hcost := (M6.Euclid.preprocess_correct_cost N a b (M6.Cyclic.modulus N) ha hb hM).2
  unfold M6.ActualTransfer.actualDistanceWork
  exact M6.Transfer.distance_work_bound (M6.ActualTransfer.span a b) N _ hspan hcost

theorem M6.ActualTransfer.actual_witness_work : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.span a b < N → M6.ActualTransfer.solve N a b = some (d,v,k) → M6.ActualTransfer.actualWitnessWork N a b k ≤ 200000*N^4*4^(M6.ActualTransfer.span a b) := by
  intro N inst a b d v k hspan hsolve
  have ha : a.natDegree ≤ N := by
    have h : max a.natDegree b.natDegree < N := hspan
    exact (le_max_left _ _).trans (Nat.le_of_lt h)
  have hb : b.natDegree ≤ N := by
    have h : max a.natDegree b.natDegree < N := hspan
    exact (le_max_right _ _).trans (Nat.le_of_lt h)
  have hM : (M6.Cyclic.modulus N).natDegree ≤ N := by
    change (Polynomial.X ^ N + 1 : Polynomial (ZMod 2)).natDegree ≤ N
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have he := (M6.Euclid.preprocess_correct_cost N a b (M6.Cyclic.modulus N) ha hb hM).2
  have hk := M6.ActualTransfer.actual_solve_queries N a b d v k hsolve
  unfold M6.ActualTransfer.actualWitnessWork
  exact M6.Transfer.witness_work_bound (M6.ActualTransfer.span a b) N _ k hspan he hk

theorem M6.RecipeIsometries.conv_multiply : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u h) = M6.RecipeIsometries.multiply N u (M6.Physical.conv N a h) := by
  intro N _ u a h
  classical
  funext i
  change (∑ j : ZMod N, a ((↑(u⁻¹) : ZMod N) * j) * h ((↑(u⁻¹) : ZMod N) * (i - j))) =
    ∑ k : ZMod N, a k * h ((↑(u⁻¹) : ZMod N) * i - k)
  calc
    _ = ∑ k : ZMod N, a ((↑(u⁻¹) : ZMod N) * ((↑u : ZMod N) * k)) *
        h ((↑(u⁻¹) : ZMod N) * (i - (↑u : ZMod N) * k)) :=
      (Equiv.sum_comp u.mulLeft (fun j : ZMod N =>
        a ((↑(u⁻¹) : ZMod N) * j) * h ((↑(u⁻¹) : ZMod N) * (i - j)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [mul_sub, ← mul_assoc]

theorem M6.RecipeIsometries.conv_shift : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s h) = M6.RecipeIsometries.shift N (r+s) (M6.Physical.conv N a h) := by
  intro N inst r s a h
  classical
  funext i
  change Finset.sum Finset.univ (fun k : ZMod N => a (k - r) * h (i - k - s)) =
    Finset.sum Finset.univ (fun k : ZMod N => a k * h (i - (r + s) - k))
  refine (Equiv.sum_comp (Equiv.addRight r)
    (fun k : ZMod N => a (k - r) * h (i - k - s))).symm.trans ?_
  change Finset.sum Finset.univ (fun k : ZMod N => a (k + r - r) * h (i - (k + r) - s)) = _
  apply Finset.sum_congr rfl
  intro k hk
  have hi : i - (k + r) - s = i - (r + s) - k := by ring
  simp only [add_sub_cancel_right, hi]

theorem M6.RecipeIsometries.exchange_laws : ∀ (N : ℕ) [NeZero N] (a b h : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.boundary N b a h = M6.RecipeIsometries.exchange N (M6.Physical.boundary N a b h) ∧ M6.Physical.syndrome N b a (M6.RecipeIsometries.exchange N z) = M6.Physical.syndrome N a b z := by
  intro N inst a b h z
  constructor
  · rfl
  · unfold M6.Physical.syndrome M6.RecipeIsometries.exchange
    funext i
    exact add_comm _ _

theorem M6.RecipeIsometries.exchange_weight : ∀ (N : ℕ) [NeZero N] (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.exchange N z) = M6.Physical.wordWeight N z := by
  intro N inst z
  change M6.Physical.weight N z.2 + M6.Physical.weight N z.1 = M6.Physical.weight N z.1 + M6.Physical.weight N z.2
  exact Nat.add_comm _ _

theorem M6.RecipeIsometries.lift_transport : ∀ (N : ℕ) [NeZero N] (a b a1 b1 : M6.RecipeIsometries.Block N) (P : M6.RecipeIsometries.Word N → M6.RecipeIsometries.Word N) (H : M6.RecipeIsometries.Block N → M6.RecipeIsometries.Block N), Function.Bijective P → Function.Surjective H → (∀ h, M6.Physical.boundary N a1 b1 (H h) = P (M6.Physical.boundary N a b h)) → (∀ z, M6.Physical.syndrome N a1 b1 (P z) = 0 ↔ M6.Physical.syndrome N a b z = 0) → (∀ z, M6.Physical.wordWeight N (P z) = M6.Physical.wordWeight N z) → Function.Bijective (M6.RecipeIsometries.lift N P) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.lift N P) v ∈ M6.Spaces.boundaryWords N (a1) (b1) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.lift N P) v ∈ M6.Spaces.cycleWords N (a1) (b1) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.lift N P) v) = M6.Pinned.weight v := by
  intro N inst a b a1 b1 P H hP hH hB hC hW
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro x y h
    have h' := congrArg (M6.Flatten.unflatten N) h
    simpa only [M6.Flatten.flatten_left] using h'
  have hu : Function.Injective (M6.Flatten.unflatten N) := by
    intro x y h
    have h' := congrArg (M6.Flatten.flatten N) h
    simpa only [M6.Flatten.flatten_right] using h'
  constructor
  · constructor
    · intro x y h
      apply hu
      apply hP.1
      apply hf
      exact h
    · intro v
      obtain ⟨z, hz⟩ := hP.2 (M6.Flatten.unflatten N v)
      refine ⟨M6.Flatten.flatten N z, ?_⟩
      simp only [M6.RecipeIsometries.lift, M6.Flatten.flatten_left, hz,
        M6.Flatten.flatten_right]
  · intro v
    constructor
    · rw [M6.Spaces.boundary_words_iff, M6.Spaces.boundary_words_iff]
      constructor
      · rintro ⟨k, hk⟩
        obtain ⟨h, rfl⟩ := hH k
        rw [hB h] at hk
        change M6.Flatten.flatten N (P (M6.Physical.boundary N a b h)) =
          M6.Flatten.flatten N (P (M6.Flatten.unflatten N v)) at hk
        have he := hP.1 (hf hk)
        refine ⟨h, ?_⟩
        exact (congrArg (M6.Flatten.flatten N) he).trans
          (M6.Flatten.flatten_right N v)
      · rintro ⟨h, hh⟩
        have he : M6.Physical.boundary N a b h = M6.Flatten.unflatten N v := by
          have he' := congrArg (M6.Flatten.unflatten N) hh
          simpa only [M6.Flatten.flatten_left] using he'
        refine ⟨H h, ?_⟩
        rw [hB h, he]
        rfl
    · constructor
      · simp only [M6.Spaces.cycle_words_iff, M6.RecipeIsometries.lift,
          M6.Flatten.flatten_left]
        exact hC (M6.Flatten.unflatten N v)
      · change M6.Pinned.weight
          (M6.Flatten.flatten N (P (M6.Flatten.unflatten N v))) =
          M6.Pinned.weight v
        rw [M6.Flatten.flatten_weight, hW]
        calc
          M6.Physical.wordWeight N (M6.Flatten.unflatten N v) =
              M6.Pinned.weight (M6.Flatten.flatten N (M6.Flatten.unflatten N v)) :=
            (M6.Flatten.flatten_weight N (M6.Flatten.unflatten N v)).symm
          _ = M6.Pinned.weight v := by rw [M6.Flatten.flatten_right]

theorem M6.RecipeIsometries.multiply_laws : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.multiply N 1 a = a ∧ M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) = a ∧ (M6.RecipeIsometries.multiply N u a = 0 ↔ a = 0) := by
  intro N inst u a
  have hinv : M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) = a := by
    funext i
    simp [M6.RecipeIsometries.multiply, ← mul_assoc]
  refine ⟨?_, hinv, ?_⟩
  · funext i
    simp [M6.RecipeIsometries.multiply]
  · constructor
    · intro h
      calc
        a = M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) := hinv.symm
        _ = M6.RecipeIsometries.multiply N (u⁻¹) 0 := congrArg (M6.RecipeIsometries.multiply N (u⁻¹)) h
        _ = 0 := rfl
    · intro h
      subst a
      rfl

theorem M6.RecipeIsometries.permutation_weight : ∀ (N : ℕ) [NeZero N] (e : Equiv.Perm (ZMod N)) (a : M6.RecipeIsometries.Block N), M6.Physical.weight N (fun i => a (e i)) = M6.Physical.weight N a := by
  change ∀ (N : ℕ) [NeZero N] (e : Equiv.Perm (ZMod N)) (a : M6.RecipeIsometries.Block N), M6.Physical.weight N (fun i => a (e i)) = M6.Physical.weight N a
  intro N _ e a
  classical
  unfold M6.Physical.weight
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i hi j hj hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simpa using hj

theorem M6.RecipeIsometries.shift_laws : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.shift N 0 a = a ∧ M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) = a ∧ (M6.RecipeIsometries.shift N r a = 0 ↔ a = 0) := by
  intro N inst r a
  have hinv (b : M6.RecipeIsometries.Block N) :
      M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r b) = b := by
    funext i
    simp [M6.RecipeIsometries.shift, sub_eq_add_neg, add_assoc]
  refine ⟨?_, hinv a, ?_⟩
  · funext i
    simp [M6.RecipeIsometries.shift]
  · constructor
    · intro h
      calc
        a = M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) := (hinv a).symm
        _ = M6.RecipeIsometries.shift N (-r) 0 := congrArg (M6.RecipeIsometries.shift N (-r)) h
        _ = 0 := rfl
    · intro h
      subst a
      rfl

theorem M6.RecipeIsometries.exchange_isometry : ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N), Function.Bijective (M6.RecipeIsometries.blockExchange N) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.boundaryWords N (b) (a) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.cycleWords N (b) (a) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.blockExchange N) v) = M6.Pinned.weight v := by
  intro N inst a b
  have hinv : ∀ z : M6.RecipeIsometries.Word N,
      M6.RecipeIsometries.exchange N (M6.RecipeIsometries.exchange N z) = z := by
    intro z
    cases z
    rfl
  refine M6.RecipeIsometries.lift_transport N a b b a
    (M6.RecipeIsometries.exchange N) (fun h => h) ?_ ?_ ?_ ?_ ?_
  · constructor
    · intro x y h
      have he := congrArg (M6.RecipeIsometries.exchange N) h
      simpa only [hinv] using he
    · intro z
      exact ⟨M6.RecipeIsometries.exchange N z, hinv z⟩
  · intro h
    exact ⟨h, rfl⟩
  · intro h
    exact (M6.RecipeIsometries.exchange_laws N a b h (0 : M6.RecipeIsometries.Word N)).1
  · intro z
    rw [(M6.RecipeIsometries.exchange_laws N a b a z).2]
  · exact M6.RecipeIsometries.exchange_weight N

theorem M6.RecipeIsometries.multiplied_boundary : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a b h : M6.RecipeIsometries.Block N), M6.Physical.boundary N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) (M6.RecipeIsometries.multiply N u h) = M6.RecipeIsometries.multiplyWord N u (M6.Physical.boundary N a b h) := by
  intro N _ u a b h
  simp only [M6.Physical.boundary, M6.RecipeIsometries.multiplyWord,
    M6.RecipeIsometries.conv_multiply]

theorem M6.RecipeIsometries.multiplied_syndrome : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a b : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.syndrome N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) (M6.RecipeIsometries.multiplyWord N u z) = M6.RecipeIsometries.multiply N u (M6.Physical.syndrome N a b z) := by
  intro N _ u a b z
  unfold M6.Physical.syndrome M6.RecipeIsometries.multiplyWord
  dsimp only
  rw [M6.RecipeIsometries.conv_multiply, M6.RecipeIsometries.conv_multiply]
  rfl

theorem M6.RecipeIsometries.multiplied_weight : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.multiplyWord N u z) = M6.Physical.wordWeight N z := by
  change ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.multiplyWord N u z) = M6.Physical.wordWeight N z
  intro N _ u z
  exact congrArg₂ Nat.add
    (M6.RecipeIsometries.permutation_weight N (u⁻¹).mulLeft z.1)
    (M6.RecipeIsometries.permutation_weight N (u⁻¹).mulLeft z.2)

theorem M6.RecipeIsometries.translated_boundary : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a b h : M6.RecipeIsometries.Block N), M6.Physical.boundary N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) h = M6.RecipeIsometries.translateWord N r s (M6.Physical.boundary N a b h) := by
  intro N inst r s a b h
  have ha := M6.RecipeIsometries.conv_shift N r 0 a h
  have hb := M6.RecipeIsometries.conv_shift N s 0 b h
  simp only [(M6.RecipeIsometries.shift_laws N 0 h).1, add_zero] at ha hb
  simp only [M6.Physical.boundary, M6.RecipeIsometries.translateWord, ha, hb]

theorem M6.RecipeIsometries.translated_syndrome : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a b : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.syndrome N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) (M6.RecipeIsometries.translateWord N r s z) = M6.RecipeIsometries.shift N (r+s) (M6.Physical.syndrome N a b z) := by
  intro N inst r s a b z
  change M6.Physical.conv N (M6.RecipeIsometries.shift N s b) (M6.RecipeIsometries.shift N r z.1) + M6.Physical.conv N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s z.2) = M6.RecipeIsometries.shift N (r + s) (M6.Physical.conv N b z.1 + M6.Physical.conv N a z.2)
  rw [M6.RecipeIsometries.conv_shift, M6.RecipeIsometries.conv_shift, add_comm s r]
  rfl

theorem M6.RecipeIsometries.translated_weight : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.translateWord N r s z) = M6.Physical.wordWeight N z := by
  intro N _ r s z
  change M6.Physical.weight N (M6.RecipeIsometries.shift N r z.1) + M6.Physical.weight N (M6.RecipeIsometries.shift N s z.2) = M6.Physical.weight N z.1 + M6.Physical.weight N z.2
  have h (t : ZMod N) (a : M6.RecipeIsometries.Block N) : M6.Physical.weight N (M6.RecipeIsometries.shift N t a) = M6.Physical.weight N a := by
    have hf : M6.RecipeIsometries.shift N t a = fun i => a ((Equiv.addRight (-t)) i) := by
      funext i
      exact congrArg a (sub_eq_add_neg i t)
    rw [hf]
    exact M6.RecipeIsometries.permutation_weight N (Equiv.addRight (-t)) a
  exact congrArg₂ (fun a b : ℕ => a + b) (h r z.1) (h s z.2)

theorem M6.RecipeIsometries.multiplier_isometry : ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (u : (ZMod N)ˣ), Function.Bijective (M6.RecipeIsometries.multiplier N u) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.multiplier N u) v) = M6.Pinned.weight v := by
  intro N inst a b u
  have hInv (t : (ZMod N)ˣ) (z : M6.RecipeIsometries.Word N) :
      M6.RecipeIsometries.multiplyWord N t⁻¹
        (M6.RecipeIsometries.multiplyWord N t z) = z := by
    apply Prod.ext
    · exact (M6.RecipeIsometries.multiply_laws N t z.1).2.1
    · exact (M6.RecipeIsometries.multiply_laws N t z.2).2.1
  refine M6.RecipeIsometries.lift_transport N a b
    (M6.RecipeIsometries.multiply N u a)
    (M6.RecipeIsometries.multiply N u b)
    (M6.RecipeIsometries.multiplyWord N u)
    (M6.RecipeIsometries.multiply N u) ?_ ?_ ?_ ?_ ?_
  · constructor
    · intro x y h
      calc
        x = M6.RecipeIsometries.multiplyWord N u⁻¹
            (M6.RecipeIsometries.multiplyWord N u x) := (hInv u x).symm
        _ = M6.RecipeIsometries.multiplyWord N u⁻¹
            (M6.RecipeIsometries.multiplyWord N u y) :=
          congrArg (M6.RecipeIsometries.multiplyWord N u⁻¹) h
        _ = y := hInv u y
    · intro z
      refine ⟨M6.RecipeIsometries.multiplyWord N u⁻¹ z, ?_⟩
      simpa only [inv_inv] using hInv u⁻¹ z
  · intro h
    refine ⟨M6.RecipeIsometries.multiply N u⁻¹ h, ?_⟩
    simpa only [inv_inv] using
      (M6.RecipeIsometries.multiply_laws N u⁻¹ h).2.1
  · exact M6.RecipeIsometries.multiplied_boundary N u a b
  · intro z
    rw [M6.RecipeIsometries.multiplied_syndrome]
    exact (M6.RecipeIsometries.multiply_laws N u
      (M6.Physical.syndrome N a b z)).2.2
  · exact M6.RecipeIsometries.multiplied_weight N u

theorem M6.RecipeIsometries.translation_isometry : ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (r s : ZMod N), Function.Bijective (M6.RecipeIsometries.translate N r s) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.translate N r s) v) = M6.Pinned.weight v := by
  intro N inst a b r s
  have hinv (t u : ZMod N) (z : M6.RecipeIsometries.Word N) :
      M6.RecipeIsometries.translateWord N (-t) (-u)
        (M6.RecipeIsometries.translateWord N t u z) = z := by
    apply Prod.ext
    · exact (M6.RecipeIsometries.shift_laws N t z.1).2.1
    · exact (M6.RecipeIsometries.shift_laws N u z.2).2.1
  refine M6.RecipeIsometries.lift_transport N a b
    (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b)
    (M6.RecipeIsometries.translateWord N r s) (fun h => h) ?_ ?_ ?_ ?_ ?_
  · constructor
    · intro x y h
      have he := congrArg (M6.RecipeIsometries.translateWord N (-r) (-s)) h
      simpa only [hinv] using he
    · intro z
      refine ⟨M6.RecipeIsometries.translateWord N (-r) (-s) z, ?_⟩
      simpa only [neg_neg] using hinv (-r) (-s) z
  · intro h
    exact ⟨h, rfl⟩
  · intro h
    exact M6.RecipeIsometries.translated_boundary N r s a b h
  · intro z
    rw [M6.RecipeIsometries.translated_syndrome]
    exact (M6.RecipeIsometries.shift_laws N (r + s)
      (M6.Physical.syndrome N a b z)).2.2
  · exact M6.RecipeIsometries.translated_weight N r s

theorem M6.EuclidStorage.control_encoding : ∀ (width v : ℕ), v ≤ 32*width → v < 2 ^ (M6.EuclidStorage.registerBits width) := by
  change ∀ (width v : ℕ), v ≤ 32 * width → v < 2 ^ (M6.EuclidStorage.registerBits width)
  intro width v hv
  have h : width < 2 ^ width := Nat.lt_two_pow_self
  change v < 2 ^ (width + 5)
  rw [pow_add]
  norm_num
  omega

theorem M6.EuclidStorage.layout_bound : ∀ N : ℕ, M6.EuclidStorage.polynomialSlots.length = 4 ∧ M6.EuclidStorage.controlSlots.length = 16 ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512*(N+1)^2 := by
  change ∀ N : ℕ, M6.EuclidStorage.polynomialSlots.length = 4 ∧ M6.EuclidStorage.controlSlots.length = 16 ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512 * (N + 1) ^ 2
  intro N
  refine ⟨rfl, rfl, ?_⟩
  norm_num [M6.EuclidStorage.actualPreprocessStorage, M6.EuclidStorage.registerBits, M6.EuclidStorage.polynomialSlots, M6.EuclidStorage.controlSlots] <;> nlinarith [Nat.zero_le (N * N)]

theorem M6.EuclidStorage.rem_loop_refines : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t : ℕ), let r := M6.EuclidStorage.remLoop fuel s c t; r.slots.p = s.p ∧ r.slots.q = s.q ∧ r.slots.saved = s.saved ∧ r.slots.work = (M6.Euclid.remainderAux fuel s.work s.q).value ∧ r.cancellations = c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ∧ r.rounds = 0 ∧ r.passes = t + (M6.Euclid.remainderAux fuel s.work s.q).passes := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t : ℕ), let r := M6.EuclidStorage.remLoop fuel s c t; r.slots.p = s.p ∧ r.slots.q = s.q ∧ r.slots.saved = s.saved ∧ r.slots.work = (M6.Euclid.remainderAux fuel s.work s.q).value ∧ r.cancellations = c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ∧ r.rounds = 0 ∧ r.passes = t + (M6.Euclid.remainderAux fuel s.work s.q).passes
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t
      simp [M6.EuclidStorage.remLoop, M6.Euclid.remainderAux]
  | succ fuel ih =>
      intro s c t
      simp only [M6.EuclidStorage.remLoop, M6.Euclid.remainderAux]
      split <;> simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem M6.EuclidStorage.slots_encoding : ∀ (N : ℕ) (s u : M6.EuclidStorage.Slots), M6.EuclidStorage.slotsFit (N+1) s → M6.EuclidStorage.slotsFit (N+1) u → M6.Euclid.dense N s.p = M6.Euclid.dense N u.p → M6.Euclid.dense N s.q = M6.Euclid.dense N u.q → M6.Euclid.dense N s.work = M6.Euclid.dense N u.work → M6.Euclid.dense N s.saved = M6.Euclid.dense N u.saved → s = u := by
  intro N s u hs hu hp hq hw hm
  rcases hs with ⟨hsp, hsq, hsw, hsm⟩
  rcases hu with ⟨hup, huq, huw, hum⟩
  have ep := M6.Euclid.dense_injective N s.p u.p hsp hup hp
  have eq := M6.Euclid.dense_injective N s.q u.q hsq huq hq
  have ew := M6.Euclid.dense_injective N s.work u.work hsw huw hw
  have em := M6.Euclid.dense_injective N s.saved u.saved hsm hum hm
  cases s
  cases u
  simp_all

theorem M6.EuclidStorage.control_values_fit : ∀ (width : ℕ) (s : M6.EuclidStorage.Slots) (fuel c e t : ℕ), M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c ≤ 32*width → e ≤ 32*width → t ≤ 32*width → ∀ v ∈ M6.EuclidStorage.controlValues s fuel c e t, v < 2 ^ (M6.EuclidStorage.registerBits width) := by
  change ∀ (width : ℕ) (s : M6.EuclidStorage.Slots) (fuel c e t : ℕ), M6.EuclidStorage.slotsFit width s → fuel ≤ 32 * width → c ≤ 32 * width → e ≤ 32 * width → t ≤ 32 * width → ∀ v ∈ M6.EuclidStorage.controlValues s fuel c e t, v < 2 ^ M6.EuclidStorage.registerBits width
  intro width s fuel c e t hs hf hc he ht v hv
  apply M6.EuclidStorage.control_encoding width v
  simp only [M6.EuclidStorage.slotsFit, M6.Euclid.rank] at hs
  simp only [M6.EuclidStorage.controlValues, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, M6.Euclid.rank] at hv
  split_ifs at hs hv <;> simp_all <;> omega

theorem M6.EuclidStorage.gcd_loop_refines : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t : ℕ), s.work = 0 → let r := M6.EuclidStorage.gcdLoop fuel s c e t; r.slots.saved = s.saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclidAux fuel s.p s.q) c e t := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t : ℕ), s.work = 0 → let r := M6.EuclidStorage.gcdLoop fuel s c e t; r.slots.saved = s.saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclidAux fuel s.p s.q) c e t
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c e t hw
      simp [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
        M6.EuclidStorage.toRun, M6.EuclidStorage.offset, hw]
  | succ fuel ih =>
      intro s c e t hw
      by_cases hq : s.q = 0
      · simp [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
          M6.EuclidStorage.toRun, M6.EuclidStorage.offset, hq, hw]
      · have hr := fun (c t : ℕ) =>
          M6.EuclidStorage.rem_loop_refines (M6.Euclid.rank s.p)
            (⟨0, s.q, s.p, s.saved⟩ : M6.EuclidStorage.Slots) c t
        dsimp only at hr
        simp only [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
          hq, if_false]
        simp only [M6.Euclid.remainder, hr, ih]
        simp [M6.EuclidStorage.offset, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]

theorem M6.EuclidStorage.rem_loop_safe : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ≤ 32*width → t + (M6.Euclid.remainderAux fuel s.work s.q).passes ≤ 32*width → M6.EuclidStorage.remSafe fuel s c t width := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ≤ 32*width → t + (M6.Euclid.remainderAux fuel s.work s.q).passes ≤ 32*width → M6.EuclidStorage.remSafe fuel s c t width
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t width hwidth hs hf hc ht
      simp [M6.Euclid.remainderAux] at hc ht
      simp [M6.EuclidStorage.remSafe]
      simp only [M6.EuclidStorage.slotsFit] at hs ⊢
      repeat' constructor <;> omega
  | succ fuel ih =>
      intro s c t width hwidth hs hf hc ht
      by_cases hw : s.work = 0
      · simp [M6.Euclid.remainderAux, hw] at hc ht
        simp [M6.EuclidStorage.remSafe, hw]
        simp only [M6.EuclidStorage.slotsFit] at hs ⊢
        repeat' constructor <;> omega
      · by_cases hq : s.q = 0
        · simp [M6.Euclid.remainderAux, hw, hq] at hc ht
          simp [M6.EuclidStorage.remSafe, hw, hq]
          simp only [M6.EuclidStorage.slotsFit] at hs ⊢
          repeat' constructor <;> omega
        · by_cases hd : s.work.degree < s.q.degree
          · simp [M6.Euclid.remainderAux, hw, hq, hd] at hc ht
            simp [M6.EuclidStorage.remSafe, hw, hq, hd]
            simp only [M6.EuclidStorage.slotsFit] at hs ⊢
            repeat' constructor <;> omega
          · have hle : s.q.degree ≤ s.work.degree := le_of_not_gt hd
            have hdrop := M6.Euclid.cancel_drop s.work s.q hw hq hle
            have hs' : M6.EuclidStorage.slotsFit width
                { s with work := M6.Euclid.cancel s.work s.q } := by
              simp only [M6.EuclidStorage.slotsFit] at hs ⊢
              repeat' constructor <;> omega
            simp [M6.Euclid.remainderAux, hw, hq, hd] at hc ht
            have hrec := ih { s with work := M6.Euclid.cancel s.work s.q }
              (c + 1) (t + 2) width hwidth hs' (by omega)
              (by dsimp; omega) (by dsimp; omega)
            simp only [M6.EuclidStorage.remSafe]
            simp only [hw, hq, hd, ite_true, ite_false, false_or, or_false,
              false_and, and_false, true_and, and_true, not_false_eq_true]
            simp only [M6.EuclidStorage.slotsFit] at hs ⊢
            repeat' first | assumption | apply And.intro | omega

theorem M6.EuclidStorage.gcd_loop_safe : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → s.work = 0 → fuel ≤ 32*width → c + (M6.Euclid.euclidAux fuel s.p s.q).cancellations ≤ 32*width → e + (M6.Euclid.euclidAux fuel s.p s.q).rounds ≤ 32*width → t + (M6.Euclid.euclidAux fuel s.p s.q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe fuel s c e t width := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → s.work = 0 → fuel ≤ 32*width → c + (M6.Euclid.euclidAux fuel s.p s.q).cancellations ≤ 32*width → e + (M6.Euclid.euclidAux fuel s.p s.q).rounds ≤ 32*width → t + (M6.Euclid.euclidAux fuel s.p s.q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe fuel s c e t width
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  have hp (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).1
  have hq' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.1
  have hsaved (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.2.1
  have hwork (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.1
  have hcancel (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.2.1
  have hpasses (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.2.2.2
  have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
    simp [M6.Euclid.rank]
  intro fuel
  induction fuel with
  | zero =>
      intro s c e t width hwidth hs hw hf hc he ht
      simp [M6.Euclid.euclidAux] at hc he ht
      simp [M6.EuclidStorage.gcdSafe]
      simp only [M6.EuclidStorage.slotsFit] at hs ⊢
      repeat' constructor <;> omega
  | succ fuel ih =>
      intro s c e t width hwidth hs hw hf hc he ht
      by_cases hq : s.q = 0
      · simp [M6.Euclid.euclidAux, hq] at hc he ht
        simp [M6.EuclidStorage.gcdSafe, hq]
        simp only [M6.EuclidStorage.slotsFit] at hs ⊢
        repeat' constructor <;> omega
      · have hb := M6.Euclid.remainder_aux_correct
          (M6.Euclid.rank s.p) s.p s.q (le_refl _)
        have ht' := M6.Euclid.remainder_passes
          (M6.Euclid.rank s.p) s.p s.q
        have hd := (M6.Euclid.remainder_correct s.p s.q).2.2 hq
        simp only [M6.Euclid.remainder] at hd
        simp [M6.Euclid.euclidAux, hq, M6.Euclid.remainder] at hc he ht
        simp only [M6.EuclidStorage.gcdSafe, hq, ite_false]
        simp only [M6.EuclidStorage.slotsFit, hp, hq', hsaved,
          hwork, hcancel, hpasses, M6.Euclid.remainder,
          Nat.zero_add, Nat.add_zero, hz] at hs ⊢
        repeat' first
          | assumption
          | apply And.intro
          | apply ih
          | apply M6.EuclidStorage.rem_loop_safe
        all_goals
          simp only [M6.EuclidStorage.slotsFit, hp, hq', hsaved,
            hwork, hcancel, hpasses, M6.Euclid.remainder,
            Nat.zero_add, Nat.add_zero, hz] at *
        all_goals omega

theorem M6.EuclidStorage.gcd_start_refines : ∀ (p q saved : M6.Euclid.BP) (c e t : ℕ), let r := M6.EuclidStorage.gcdStart p q saved c e t; r.slots.saved = saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclid p q) c e t := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (p q saved : M6.Euclid.BP) (c e t : ℕ), let r := M6.EuclidStorage.gcdStart p q saved c e t; r.slots.saved = saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclid p q) c e t
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro p q saved c e t
  simpa [M6.EuclidStorage.gcdStart, M6.Euclid.euclid,
    M6.EuclidStorage.offset, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (M6.EuclidStorage.gcd_loop_refines (M6.Euclid.rank q + 1)
      (⟨p, q, 0, saved⟩ : M6.EuclidStorage.Slots) c e (t + 1) rfl)

theorem M6.EuclidStorage.gcd_start_safe : ∀ (p q saved : M6.Euclid.BP) (c e t width : ℕ), 0 < width → M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.rank saved ≤ width → c + (M6.Euclid.euclid p q).cancellations ≤ 32*width → e + (M6.Euclid.euclid p q).rounds ≤ 32*width → t + (M6.Euclid.euclid p q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe (M6.Euclid.rank q+1) ⟨p,q,0,saved⟩ c e (t+1) width := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (p q saved : M6.Euclid.BP) (c e t width : ℕ), 0 < width → M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.rank saved ≤ width → c + (M6.Euclid.euclid p q).cancellations ≤ 32*width → e + (M6.Euclid.euclid p q).rounds ≤ 32*width → t + (M6.Euclid.euclid p q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe (M6.Euclid.rank q+1) ⟨p,q,0,saved⟩ c e (t+1) width
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro p q saved c e t width hwidth hp hq hs hc he ht
  have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
    simp [M6.Euclid.rank]
  dsimp [M6.Euclid.euclid] at hc he ht
  apply M6.EuclidStorage.gcd_loop_safe
  · exact hwidth
  · simp [M6.EuclidStorage.slotsFit, hz, hp, hq, hs]
  · rfl
  · omega
  · exact hc
  · exact he
  · dsimp only
    omega

theorem M6.EuclidStorage.preprocess_refines : ∀ a b M : M6.Euclid.BP, M6.EuclidStorage.toRun (M6.EuclidStorage.preprocess a b M) = M6.Euclid.preprocess a b M := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ a b M : M6.Euclid.BP, M6.EuclidStorage.toRun (M6.EuclidStorage.preprocess a b M) = M6.Euclid.preprocess a b M
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro a b M
  have hfirst := M6.EuclidStorage.gcd_start_refines a b M 0 0 0
  have hs := hfirst.1
  have hv := congrArg M6.Euclid.Run.value hfirst.2.2
  have hc := congrArg M6.Euclid.Run.cancellations hfirst.2.2
  have he := congrArg M6.Euclid.Run.rounds hfirst.2.2
  have ht := congrArg M6.Euclid.Run.passes hfirst.2.2
  simp only [M6.EuclidStorage.toRun, M6.EuclidStorage.offset,
    Nat.zero_add, Nat.add_zero] at hv hc he ht
  have hsecond := fun p q saved c e t =>
    (M6.EuclidStorage.gcd_start_refines p q saved c e t).2.2
  dsimp only [M6.EuclidStorage.preprocess]
  rw [hsecond]
  simp [M6.Euclid.preprocess, M6.EuclidStorage.offset,
    hs, hv, hc, he, ht, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem M6.EuclidStorage.preprocess_safe : ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → M6.EuclidStorage.preprocessSafe (N+1) a b M := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → M6.EuclidStorage.preprocessSafe (N+1) a b M
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N a b M ha hb hM
  have rank_bound (p : M6.Euclid.BP) (hp : p.natDegree ≤ N) :
      M6.Euclid.rank p ≤ N + 1 := by
    unfold M6.Euclid.rank
    split <;> omega
  have ha' := rank_bound a ha
  have hb' := rank_bound b hb
  have hM' := rank_bound M hM
  have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
    simp [M6.Euclid.rank]
  have bounds (p q : M6.Euclid.BP)
      (hp : M6.Euclid.rank p ≤ N + 1)
      (hq : M6.Euclid.rank q ≤ N + 1) :
      (M6.Euclid.euclid p q).cancellations ≤ 2 * (N + 1) ∧
      (M6.Euclid.euclid p q).rounds ≤ N + 1 ∧
      (M6.Euclid.euclid p q).passes ≤ 9 * (N + 1) := by
    have h := M6.Euclid.euclid_correct p q
    have ht := M6.Euclid.euclid_passes p q
    omega
  have hfirst := bounds a b ha' hb'
  have hout : M6.Euclid.rank (M6.Euclid.euclid a b).value ≤ N + 1 := by
    have h := M6.Euclid.euclid_output_width (M6.Euclid.rank b + 1) a b
    have hm : max (M6.Euclid.rank a) (M6.Euclid.rank b) ≤ N + 1 :=
      max_le ha' hb'
    simpa only [M6.Euclid.euclid] using h.trans hm
  have hsecond := bounds (M6.Euclid.euclid a b).value M hout hM'
  have hr := M6.EuclidStorage.gcd_start_refines a b M 0 0 0
  have hs := hr.1
  have hv := congrArg (fun r : M6.Euclid.Run => r.value) hr.2.2
  have hc := congrArg (fun r : M6.Euclid.Run => r.cancellations) hr.2.2
  have he := congrArg (fun r : M6.Euclid.Run => r.rounds) hr.2.2
  have ht := congrArg (fun r : M6.Euclid.Run => r.passes) hr.2.2
  simp only [M6.EuclidStorage.toRun, M6.EuclidStorage.offset,
    Nat.zero_add, Nat.add_zero] at hv hc he ht
  unfold M6.EuclidStorage.preprocessSafe
  dsimp only
  simp only [hs, hv, hc, he, ht]
  constructor <;> apply M6.EuclidStorage.gcd_start_safe <;> omega

theorem M6.EuclidStorage.preprocess_storage : ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → M6.EuclidStorage.toRun (M6.EuclidStorage.preprocess a b M) = M6.Euclid.preprocess a b M ∧ M6.EuclidStorage.preprocessSafe (N+1) a b M ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512*(N+1)^2 := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → M6.EuclidStorage.toRun (M6.EuclidStorage.preprocess a b M) = M6.Euclid.preprocess a b M ∧ M6.EuclidStorage.preprocessSafe (N+1) a b M ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512*(N+1)^2
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N a b M ha hb hM
  exact ⟨M6.EuclidStorage.preprocess_refines a b M,
    M6.EuclidStorage.preprocess_safe N a b M ha hb hM,
    (M6.EuclidStorage.layout_bound N).2.2⟩

theorem M6.ActualTransfer.actual_solve_storage : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → M6.ActualTransfer.actualSolveStorage N a b ≤ 16384*N^2*2^(M6.ActualTransfer.span a b) := by
  intro N inst a b hspan
  have ha : a.natDegree ≤ N := by
    unfold M6.ActualTransfer.span at hspan
    omega
  have hb : b.natDegree ≤ N := by
    unfold M6.ActualTransfer.span at hspan
    omega
  have hM : (M6.Cyclic.modulus N).natDegree ≤ N := by
    unfold M6.Cyclic.modulus
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hstorage := M6.EuclidStorage.preprocess_storage N a b
    (M6.Cyclic.modulus N) ha hb hM
  simpa only [M6.ActualTransfer.actualSolveStorage] using
    (M6.Transfer.solve_storage_bound (M6.ActualTransfer.span a b) N
      (M6.EuclidStorage.actualPreprocessStorage N) hspan hstorage.2.2)

theorem M6.Transfer.complete_address_capacity : ∀ R N slots : ℕ, R < N → slots ≤ 512*(N+1)^2 → M6.Transfer.solveStorage R N slots < 2^(M6.Transfer.actualAddressBits R N) := by
  change ∀ R N slots : ℕ, R < N → slots ≤ 512 * (N + 1)^2 → M6.Transfer.solveStorage R N slots < 2^(M6.Transfer.actualAddressBits R N)
  intro R N slots hRN hslots
  have hNat : ∀ n : ℕ, n ≤ 2^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hp : 0 < (2 : ℕ)^n := by positivity
      rw [pow_succ]
      omega
  have hsq : N^2 ≤ ((2 : ℕ)^N)^2 := Nat.pow_le_pow_left (hNat N) 2
  have hbound := M6.Transfer.solve_storage_bound R N slots hRN hslots
  change M6.Transfer.solveStorage R N slots < 2^(R + 4*N + 16)
  calc
    M6.Transfer.solveStorage R N slots ≤ 16384 * N^2 * 2^R := hbound
    _ ≤ 16384 * ((2 : ℕ)^N)^2 * 2^R :=
      Nat.mul_le_mul_right (2^R) (Nat.mul_le_mul_left 16384 hsq)
    _ = 2^(R + (N + N) + 14) := by
      simp only [pow_add, pow_two]
      norm_num
      ring
    _ < 2^(R + 4*N + 16) := by
      apply Nat.pow_lt_pow_right
      · norm_num
      · omega

theorem M6.Transfer.recovery_stack_allocation : ∀ R N : ℕ, M6.Transfer.actualTraceStorage R N + 2*(2*N+1)*M6.Transfer.queryCoefficientBits R N + M6.Transfer.recoveryStackBits R N ≤ M6.Transfer.pairedQueryStorage R N := by
  change ∀ R N : ℕ, _
  intro R N
  by_cases h : N < 3
  · interval_cases N <;>
      simp [M6.Transfer.pairedQueryStorage, M6.Transfer.recoveryStackBits,
        M6.Transfer.queryCoefficientBits, M6.Transfer.actualAddressBits,
        M6.Transfer.coefficientBits, List.length_finRange] <;>
      ring_nf <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = k + 3 := ⟨N - 3, by omega⟩
    simp [M6.Transfer.pairedQueryStorage, M6.Transfer.recoveryStackBits,
      M6.Transfer.queryCoefficientBits, M6.Transfer.actualAddressBits,
      M6.Transfer.coefficientBits, List.length_finRange]
    ring_nf
    omega

theorem M6.Final.answer_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.AnswerCorrect N a b := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.AnswerCorrect N a b
  intro N inst a b h
  classical
  have hs : M6.ActualTransfer.span a b < N := h.2.2.2.2.1
  have ha : a.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_left a.natDegree b.natDegree) hs)
  have hb : b.degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt (Nat.le_max_right a.natDegree b.natDegree) hs)
  have solve := M6.ActualResult.solve_exact N a b hs
  have nonempty := M6.ActualCounts.logicals_nonempty_iff N a b ha hb
  have empty : M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) = ∅ ↔ M6.ActualCounts.f N a b = 0 := by
    rw [← Finset.not_nonempty_iff_eq_empty, nonempty]
    omega
  have qd : M6.Final.quantumDistance N a b = M6.Pinned.distance (M6.Final.LX N a b) := M6.ActualCSS.common_quantum_distance N _ _
  have ds := M6.Pinned.distance_spec (2*N) (M6.Final.LX N a b)
  change (_ ↔ _) ∧ (_ ↔ _) ∧ _
  refine ⟨solve.1.trans empty, ?_, ?_, ?_⟩
  · rw [qd, ds.1]; exact empty
  · intro d v k hv
    have hvp := solve.2 d v k hv
    refine ⟨?_, hvp.1, hvp.2.1, ?_, (M6.Flatten.J_weight N v).trans hvp.2.1, hvp.2.2.2⟩
    · rw [qd, ds.2 d]
      exact ⟨⟨v, hvp.1, hvp.2.1⟩, hvp.2.2.1⟩
    · exact (M6.ActualCSS.J_logical_iff N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) v).mp hvp.1
  · intro hf
    cases hh : M6.ActualTransfer.solve N a b with
    | none => have hz := (solve.1.trans empty).mp hh; omega
    | some x => rcases x with ⟨d,v,k⟩; exact ⟨d,v,k,rfl⟩

theorem M6.Final.counting_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.CountingCorrect N a b := by
  intro N inst a b h
  classical
  have hs : M6.ActualTransfer.span a b < N := h.2.2.2.2.1
  have hna : a.natDegree < N := lt_of_le_of_lt (Nat.le_max_left _ _) hs
  have hnb : b.natDegree < N := lt_of_le_of_lt (Nat.le_max_right _ _) hs
  have ha : a.degree < (N : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hna)
  have hb : b.degree < (N : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnb)
  constructor
  · intro P
    refine ⟨?_, ?_, M6.ActualResult.boundary_normalized N a b hs P,
      M6.ActualResult.cycle_normalized N a b hs P,
      M6.ActualResult.Q_enumerator N a b hs P,
      (fun d => M6.ActualResult.Q_coeff N a b hs P d),
      M6.ActualResult.Q_zero N a b hs P⟩
    · rw [M6.ActualTransfer.boundary_trace_inputs N a b hs P]
      simpa only [M6.ActualCounts.boundaryInputSum, M6.Spaces.boundary_eval, M6.Final.BX] using
        M6.ActualCounts.boundary_pinned_sum N a b ha hb P
    · rw [M6.ActualTransfer.character_trace_inputs N a b hs P]
      simpa only [M6.ActualCounts.signedInputSum, M6.Spaces.dual_boundary_eval, M6.Final.CX] using
        M6.ActualCounts.cycle_pinned_sum N a b ha hb P
  · exact (M6.ActualResult.Q_total N a b hs).trans (M6.ActualCounts.logical_card N a b ha hb)

theorem M6.Final.execution_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ExecutionCorrect N a b := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ExecutionCorrect N a b
  intro N inst a b h
  have hb := M6.ActualTransfer.boundary_indexed_resources
  have hc := M6.ActualTransfer.character_indexed_resources
  have ho := M6.ActualTransfer.shifted_output_exact
  have hs := M6.ActualTransfer.shifted_scan_exact
  first
  | have hd := M6.SolveResources.actual_distance_work
  | have hd := M6.Solve.actual_distance_work
  | have hd := M6.QueryResources.actual_distance_work
  | have hd := M6.Query.actual_distance_work
  | have hd := M6.Postprocessing.actual_distance_work
  | have hd := M6.ActualTransfer.actual_distance_work
  | have hd := M6.Final.actual_distance_work
  | have hd := M6.actual_distance_work
  first
  | have hw := M6.SolveResources.actual_witness_work
  | have hw := M6.Solve.actual_witness_work
  | have hw := M6.QueryResources.actual_witness_work
  | have hw := M6.Query.actual_witness_work
  | have hw := M6.Postprocessing.actual_witness_work
  | have hw := M6.ActualTransfer.actual_witness_work
  | have hw := M6.Final.actual_witness_work
  | have hw := M6.actual_witness_work
  unfold M6.Final.Admissible at h
  unfold M6.Final.ExecutionCorrect
  aesop (add safe apply [hb, hc, ho, hs, hd, hw])

theorem M6.Final.fixed_span_correct : M6.Final.FixedSpanCorrect := by
  change M6.Final.FixedSpanCorrect
  refine ⟨M6.FixedSpan.distance_improvement, M6.FixedSpan.witness_improvement, ?_⟩
  intro k
  have h := M6.FixedSpan.nontrivial_family k
  have hd := M6.FixedSpan.recipe_degree.2
  have hs : M6.ActualTransfer.span M6.FixedSpan.recipe M6.FixedSpan.recipe = 2 := by
    simp [M6.ActualTransfer.span, hd]
  refine ⟨?_, hs, h.2.2.2.2⟩
  change 0 < 3*(k+1) ∧ _
  refine ⟨by omega, ?_, ?_, rfl, ?_, ?_⟩
  · simp [M6.FixedSpan.recipe]
  · simp [M6.FixedSpan.recipe]
  · rw [hs]; exact h.1
  · simpa only [Finset.union_self] using h.2.2.2.1

theorem M6.Final.parameters_correct : ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ParametersCorrect N a b := by
  intro N inst a b h
  have hs : M6.ActualTransfer.span a b < N := h.2.2.2.2.1
  have hna : a.natDegree < N := lt_of_le_of_lt (Nat.le_max_left _ _) hs
  have hnb : b.natDegree < N := lt_of_le_of_lt (Nat.le_max_right _ _) hs
  have ha : a.degree < (N : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hna)
  have hb : b.degree < (N : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnb)
  exact ⟨M6.ActualCounts.boundary_card N a b ha hb,
    M6.ActualCounts.cycle_card N a b ha hb,
    M6.ActualCounts.encoded_dimension N a b ha hb,
    M6.ActualCounts.f_le_order N a b,
    M6.ActualCounts.logicals_nonempty_iff N a b ha hb⟩

theorem M6.Final.zero_span_correct : M6.Final.ZeroSpanCorrect := by
  change M6.Final.ZeroSpanCorrect
  refine ⟨M6.ZeroSpan.anchored_zero, M6.ZeroSpan.connected_zero, M6.ZeroSpan.boundary_loops, M6.ZeroSpan.character_loops, M6.ZeroSpan.boundary_trace_zero, M6.ZeroSpan.character_trace_zero, ?_⟩
  intro N inst
  unfold M6.ActualTransfer.Q
  rw [M6.ZeroSpan.boundary_trace_zero, M6.ZeroSpan.character_trace_zero]
  have hf : M6.ActualCounts.f N 1 1 = 0 := by
    unfold M6.ActualCounts.f
    rw [M6.ZeroSpan.signature_one]
    simp
  change M6.Normalize.divide ((2 : ℤ)^N) (Polynomial.C ((2 : ℤ)^N) * ((1 : Polynomial ℤ) + Polynomial.X^2)^N) - M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N 1 1)) (((1 : Polynomial ℤ) + Polynomial.X^2)^N) = 0
  rw [hf]
  simp only [pow_zero]
  rw [M6.Normalize.divide_scaled _ _ (pow_ne_zero _ (by norm_num))]
  have h1 := M6.Normalize.divide_scaled (1 : ℤ) (((1 : Polynomial ℤ) + Polynomial.X^2)^N) (by norm_num)
  simp only [map_one, one_mul] at h1
  rw [h1]
  exact sub_self _
