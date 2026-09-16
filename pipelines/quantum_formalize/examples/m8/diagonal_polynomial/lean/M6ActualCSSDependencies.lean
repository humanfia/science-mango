import M6ActualCSS

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
