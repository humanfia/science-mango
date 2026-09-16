import M8P4Gcd

theorem M8.P4Gcd.cofactor_eval : ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1 := by
  change ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1
  intro m
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [M8.P4Gcd.oddCofactor, Polynomial.eval_finset_sum, Nat.cast_add, Nat.cast_mul, htwo]

theorem M8.P4Gcd.factorization : ∀ m : ℕ, M6.Cyclic.modulus (4*m+2) = (Polynomial.X+1)^2 * M8.P4Gcd.oddCofactor m := by
  intro m
  have htwo : (2 : M6.Cyclic.BinaryPolynomial) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (Polynomial.C : ZMod 2 → Polynomial (ZMod 2))
        (show (2 : ZMod 2) = 0 by decide)
  have hneg : -(1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    linear_combination -htwo
  have hsquare : ((Polynomial.X : M6.Cyclic.BinaryPolynomial) + 1)^2 = Polynomial.X^2 - 1 := by
    linear_combination (Polynomial.X + 1) * htwo
  have hgeom : ∀ n : ℕ,
      ((Polynomial.X : M6.Cyclic.BinaryPolynomial)^2 - 1) *
        (Finset.range n).sum (fun i => Polynomial.X^(2*i)) =
          Polynomial.X^(2*n) - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      rw [Nat.mul_succ, pow_add]
      ring
  have hexp : 2 * (2*m+1) = 4*m+2 := by omega
  simpa [M6.Cyclic.modulus, M8.P4Gcd.oddCofactor, hsquare,
    hexp, sub_eq_add_neg, hneg] using (hgeom (2*m+1)).symm

theorem M8.P4Gcd.cofactor_coprime : ∀ m : ℕ, IsCoprime (Polynomial.X+1) (M8.P4Gcd.oddCofactor m) := by
  change ∀ m : ℕ, IsCoprime (Polynomial.X + 1) (M8.P4Gcd.oddCofactor m)
  intro m
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have hr : Polynomial.IsRoot (M8.P4Gcd.oddCofactor m - 1) (-1 : ZMod 2) := by
    change Polynomial.eval (-1) (M8.P4Gcd.oddCofactor m - 1) = 0
    rw [hneg]
    simp [M8.P4Gcd.cofactor_eval]
  have hd : Polynomial.X + 1 ∣ M8.P4Gcd.oddCofactor m - 1 := by
    simpa only [map_neg, map_one, sub_neg_eq_add] using
      (Polynomial.dvd_iff_isRoot.mpr hr)
  rcases hd with ⟨q, hq⟩
  refine ⟨-q, 1, ?_⟩
  calc
    -q * (Polynomial.X + 1) + 1 * M8.P4Gcd.oddCofactor m =
        M8.P4Gcd.oddCofactor m - (Polynomial.X + 1) * q := by ring
    _ = 1 := by rw [← hq]; ring

theorem M8.P4Gcd.gcd_two_mod_four : ∀ m : ℕ, gcd M8.P4Family.polynomial (M6.Cyclic.modulus (4*m+2)) = (Polynomial.X+1)^2 := by
  change ∀ m : ℕ, gcd M8.P4Family.polynomial (M6.Cyclic.modulus (4*m+2)) = (Polynomial.X+1)^2
  intro m
  rw [M8.P4Family.power_identity, M8.P4Gcd.factorization]
  let p : M6.Cyclic.BinaryPolynomial := Polynomial.X + 1
  let H := M8.P4Gcd.oddCofactor m
  change gcd (p^3) (p^2 * H) = p^2
  have hm : p.Monic := by
    simpa only [p, Polynomial.C_1] using (Polynomial.monic_X_add_C (1 : ZMod 2))
  have hc : IsCoprime p H := M8.P4Gcd.cofactor_coprime m
  rcases hc with ⟨a, b, hab⟩
  let d := gcd (p^3) (p^2 * H)
  have hd₁ : d ∣ p^3 := gcd_dvd_left _ _
  have hd₂ : d ∣ p^2 * H := gcd_dvd_right _ _
  have hd : d ∣ p^2 := by
    rcases hd₁ with ⟨u, hu⟩
    rcases hd₂ with ⟨v, hv⟩
    refine ⟨a*u + b*v, ?_⟩
    calc
      p^2 = p^2 * (a*p + b*H) := by rw [hab, mul_one]
      _ = a*p^3 + b*(p^2*H) := by ring
      _ = d * (a*u + b*v) := by rw [hu, hv]; ring
  have hl : p^2 ∣ p^3 := by
    refine ⟨p, ?_⟩
    ring
  have hr : p^2 ∣ p^2 * H := ⟨H, rfl⟩
  exact (gcd_eq_normalize hd (dvd_gcd hl hr)).trans ((hm.pow 2).normalize_eq_self)

theorem M8.P4Gcd.signature_even : ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M7.RecipeSignature.signature (M8.P4Family.recipe N) = if 4 ∣ N then M8.P4Family.polynomial else (Polynomial.X+1)^2 := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M7.RecipeSignature.signature (M8.P4Family.recipe N) = if 4 ∣ N then M8.P4Family.polynomial else (Polynomial.X + 1)^2
  intro N _ hN heven
  have hs : M7.RecipeSignature.signature (M8.P4Family.recipe N) =
      EuclideanDomain.gcd M8.P4Family.polynomial (M6.Cyclic.modulus N) := by
    simp only [M7.RecipeSignature.signature, M8.P4Family.recipe,
      M6.Cyclic.signature, M8.P4Family.literal_polynomial N hN,
      EuclideanDomain.gcd_self]
  have hmonic := (M7.RecipeSignature.signature_properties N (M8.P4Family.recipe N)).1
  rw [hs] at hmonic ⊢
  have hp : (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial).Monic := by
    simpa only [Polynomial.C_1] using Polynomial.monic_X_add_C (1 : ZMod 2)
  by_cases hfour : 4 ∣ N
  · rw [if_pos hfour]
    have hd := M8.P4Family.divides_four N hfour
    have hm : M8.P4Family.polynomial.Monic := by
      rw [M8.P4Family.power_identity]
      exact hp.pow 3
    apply Polynomial.eq_of_monic_of_associated hmonic hm
    exact associated_of_dvd_dvd
      (EuclideanDomain.gcd_dvd_left _ _)
      (EuclideanDomain.dvd_gcd (dvd_refl _) hd)
  · rw [if_neg hfour]
    have hmod : N % 4 ≠ 0 := by
      intro h
      exact hfour (Nat.dvd_of_mod_eq_zero h)
    have hrepr : N = 4 * (N / 4) + 2 := by
      rcases heven with ⟨k, hk⟩
      omega
    have hg : gcd M8.P4Family.polynomial (M6.Cyclic.modulus N) =
        (Polynomial.X + 1)^2 := by
      rw [hrepr]
      exact M8.P4Gcd.gcd_two_mod_four (N / 4)
    apply Polynomial.eq_of_monic_of_associated hmonic (hp.pow 2)
    apply associated_of_dvd_dvd
    · rw [← hg]
      exact dvd_gcd (EuclideanDomain.gcd_dvd_left _ _)
        (EuclideanDomain.gcd_dvd_right _ _)
    · apply EuclideanDomain.dvd_gcd
      · rw [← hg]
        exact gcd_dvd_left _ _
      · rw [← hg]
        exact gcd_dvd_right _ _

theorem M8.P4Gcd.full_multiplicity : ∀ (N : ℕ) [NeZero N], 8 ≤ N → ∀ v m : ℕ, 0 < v → Odd m → N = 2^v*m → M7.RecipeSignature.signature (M8.P4Family.recipe N) = (Polynomial.X+1)^(min 3 (2^v)) := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → ∀ v m : ℕ, 0 < v → Odd m → N = 2^v*m → M7.RecipeSignature.signature (M8.P4Family.recipe N) = (Polynomial.X+1)^(min 3 (2^v))
  intro N _ hN v m hv hm hfac
  cases v with
  | zero => omega
  | succ v =>
    cases v with
    | zero =>
      have hNm : N = 2 * m := by simpa using hfac
      have heven : Even N := ⟨m, by omega⟩
      have hfour : ¬ 4 ∣ N := by
        intro hd
        rcases hd with ⟨t, ht⟩
        rcases hm with ⟨k, hk⟩
        omega
      rw [M8.P4Gcd.signature_even N hN heven, if_neg hfour]
      norm_num
    | succ v =>
      have hpow : (2 : ℕ)^(Nat.succ (Nat.succ v)) = 4 * 2^v := by
        simp only [pow_succ]
        ring
      have hNm : N = 4 * (2^v * m) := by
        rw [hfac, hpow]
        ring
      have heven : Even N := ⟨2 * (2^v * m), by omega⟩
      have hfour : 4 ∣ N := ⟨2^v * m, hNm⟩
      have hbound : 3 ≤ (2 : ℕ)^(Nat.succ (Nat.succ v)) := by
        rw [hpow]
        have hp : 0 < (2 : ℕ)^v := pow_pos (by decide) v
        omega
      rw [M8.P4Gcd.signature_even N hN heven, if_pos hfour,
        M8.P4Family.power_identity, min_eq_left hbound]
#print axioms M8.P4Gcd.cofactor_eval
#print axioms M8.P4Gcd.cofactor_coprime
#print axioms M8.P4Gcd.factorization
#print axioms M8.P4Gcd.gcd_two_mod_four
#print axioms M8.P4Gcd.signature_even
#print axioms M8.P4Gcd.full_multiplicity
