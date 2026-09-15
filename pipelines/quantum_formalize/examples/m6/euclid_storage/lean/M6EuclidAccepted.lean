import M6Euclid

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

theorem M6.Euclid.cancel_drop : ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p := by
  change ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p
  intro p q hp hq hdeg
  apply ((M6.Euclid.rank_order (M6.Euclid.cancel p q) p).1).mpr
  have hmp := (M6.Euclid.binary_normalization p).1 hp
  have hmq := (M6.Euclid.binary_normalization q).1 hq
  simpa [M6.Euclid.cancel, hmp.leadingCoeff, mul_comm, mul_left_comm, mul_assoc] using
    (Polynomial.div_wf_lemma (p := p) (q := q) ⟨hdeg, hp⟩ hmq)

theorem M6.Euclid.cancel_mod : ∀ p q : M6.Euclid.BP, M6.Euclid.cancel p q % q = p % q := by
  change ∀ p q : M6.Euclid.BP, M6.Euclid.cancel p q % q = p % q
  intro p q
  apply Polynomial.mod_eq_of_dvd_sub
  simp [M6.Euclid.cancel, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

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

theorem M6.Euclid.euclid_correct : ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).value = GCDMonoid.gcd p q ∧ (M6.Euclid.euclid p q).cancellations ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclid p q).rounds ≤ M6.Euclid.rank q := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).value = GCDMonoid.gcd p q ∧ (M6.Euclid.euclid p q).cancellations ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclid p q).rounds ≤ M6.Euclid.rank q
  intro p q
  obtain ⟨hv, hc, hr⟩ := M6.Euclid.euclid_aux_correct (M6.Euclid.rank q + 1) p q (by omega)
  have hv' := hv.trans (M6.Euclid.normalized_gcd p q)
  have hc' : (M6.Euclid.euclidAux (M6.Euclid.rank q + 1) p q).cancellations ≤ M6.Euclid.rank p + M6.Euclid.rank q := by
    omega
  simpa only [M6.Euclid.euclid] using And.intro hv' (And.intro hc' hr)

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

theorem M6.Euclid.euclid_passes : ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).passes = 2 * (M6.Euclid.euclid p q).cancellations + 3 * (M6.Euclid.euclid p q).rounds + 2 := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).passes = 2 * (M6.Euclid.euclid p q).cancellations + 3 * (M6.Euclid.euclid p q).rounds + 2
  intro p q
  simp [M6.Euclid.euclid, M6.Euclid.euclid_aux_passes] <;> omega

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
