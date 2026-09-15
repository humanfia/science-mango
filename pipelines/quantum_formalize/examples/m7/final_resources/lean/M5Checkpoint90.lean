import M5Accepted
import M5Binomial
import M5CRT
import M5Cardinality
import M5Character
import M5Checkpoint72
import M5FactorProduct
import M5FiniteExclusion
import M5Foundation
import M5IntegerMobius
import M5Lift
import M5Packing
import M5PackingInjective
import M5Period
import M5QuotientCharacter
import M5QuotientFinite
import M5QuotientMonomialPeriod
import M5RepairSupport
import M5Signature
import M5StageOne
import M5SubsetCharacter
import M5SupportPolynomial
import M5TupleCharacter

theorem M5.SubsetCharacter.value_zero : ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1 := by
  change ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
  intro D lam
  simp [M5.Character.value, M5.Character.bitSign]

theorem M5.SubsetCharacter.character_subset_sum : ∀ (D : ℕ) (U : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.SubsetCharacter.vectorSum U f) = ∏ s ∈ U, M5.Character.value lam (f s) := by
  change ∀ (D : ℕ) (U : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.SubsetCharacter.vectorSum U f) = ∏ s ∈ U, M5.Character.value lam (f s)
  intro D U f lam
  classical
  unfold M5.SubsetCharacter.vectorSum
  induction U using Finset.induction_on with
  | empty =>
      simpa using M5.SubsetCharacter.value_zero D lam
  | @insert s U hs ih =>
      rw [Finset.sum_insert hs, Finset.prod_insert hs]
      first
      | rw [M5.Character.character_add, ih]
      | rw [M5.SubsetCharacter.character_add, ih]

theorem M5.SubsetCharacter.signed_product_expansion : ∀ (D : ℕ) (S : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s)) = ∑ U ∈ S.powerset, Polynomial.C (M5.Character.value lam (M5.SubsetCharacter.vectorSum U f)) * (Polynomial.X : Polynomial ℤ) ^ U.card := by
  change ∀ (D : ℕ) (S : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s)) = ∑ U ∈ S.powerset, Polynomial.C (M5.Character.value lam (M5.SubsetCharacter.vectorSum U f)) * (Polynomial.X : Polynomial ℤ) ^ U.card
  intro D S f lam
  classical
  unfold M5.SubsetCharacter.signedProduct
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro U hU
  clear hU
  rw [M5.SubsetCharacter.character_subset_sum]
  induction U using Finset.induction_on with
  | empty => simp
  | @insert s U hs ih =>
      rw [Finset.prod_insert hs, Finset.prod_insert hs, Finset.card_insert_of_notMem hs, ih, map_mul, pow_succ]
      ring

theorem M5.SubsetCharacter.signed_product_coefficient : ∀ (D : ℕ) (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s))).coeff k = ∑ U ∈ S.powersetCard k, M5.Character.value lam (M5.SubsetCharacter.vectorSum U f) := by
  change ∀ (D : ℕ) (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s))).coeff k = ∑ U ∈ S.powersetCard k, M5.Character.value lam (M5.SubsetCharacter.vectorSum U f)
  intro D S k f lam
  classical
  rw [M5.SubsetCharacter.signed_product_expansion]
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.powersetCard_eq_filter, Finset.sum_filter, eq_comm]

theorem M5.SubsetCharacter.subset_character_count : ∀ (D : ℕ) (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * (M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s))).coeff k) = (2 : ℤ) ^ D * (M5.SubsetCharacter.count S k f z : ℤ) := by
  change ∀ (D : ℕ) (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * (M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s))).coeff k) = (2 : ℤ) ^ D * (M5.SubsetCharacter.count S k f z : ℤ)
  intro D S k f z
  classical
  have hself (v : M5.Character.BinaryVector D) : v + v = 0 := by
    funext i
    change v i + v i = (0 : ZMod 2)
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [← two_mul, htwo, zero_mul]
  have hzero (v : M5.Character.BinaryVector D) : z + v = 0 ↔ v = z := by
    constructor
    · intro h
      have hh := congrArg (fun w : M5.Character.BinaryVector D => z + w) h
      simpa only [← add_assoc, hself, zero_add, add_zero] using hh
    · intro h
      subst v
      exact hself z
  simp_rw [M5.SubsetCharacter.signed_product_coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  first
  | simp_rw [← M5.Character.character_add]
  | simp_rw [← M5.SubsetCharacter.character_add]
  first
  | simp_rw [M5.Character.character_orthogonality]
  | simp_rw [M5.SubsetCharacter.character_orthogonality]
  simp_rw [hzero]
  rw [← Finset.sum_filter]
  simp [M5.SubsetCharacter.count, mul_comm]

theorem M5.TupleCharacter.tuple_character_count : ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (2 : ℤ) ^ D * (M5.TupleCharacter.count k f z : ℤ) := by
  classical
  intro D n k f z
  have hself : z + z = 0 := by
    ext i
    exact (show ∀ a : ZMod 2, a + a = 0 by decide) (z i)
  have hz : ∀ u : M5.Character.BinaryVector D, z + u = 0 ↔ u = z := by
    intro u
    constructor
    · intro h
      apply add_left_cancel (a := z)
      exact h.trans hself.symm
    · rintro rfl
      exact hself
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← M5.Character.character_add, M5.Character.character_orthogonality, hz]
  simp [← Finset.sum_filter, M5.TupleCharacter.count, mul_comm]

theorem M5.TupleCharacter.value_zero : ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1 := by
  change ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
  intro D lam
  simp [M5.Character.value, M5.Character.bitSign]

theorem M5.TupleCharacter.character_tuple_sum : ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (t : Fin k → Fin n) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.TupleCharacter.vectorSum f t) = ∏ i : Fin k, M5.Character.value lam (f (t i)) := by
  change ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (t : Fin k → Fin n) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.TupleCharacter.vectorSum f t) = ∏ i : Fin k, M5.Character.value lam (f (t i))
  intro D n k f t lam
  classical
  have h : ∀ s : Finset (Fin k), M5.Character.value lam (∑ i ∈ s, f (t i)) = ∏ i ∈ s, M5.Character.value lam (f (t i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty, Finset.prod_empty] using M5.TupleCharacter.value_zero D lam
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha]
        first
        | rw [M5.TupleCharacter.character_add]
        | rw [M5.Character.character_add]
        rw [ih]
  simpa [M5.TupleCharacter.vectorSum, Finset.sum_apply] using h Finset.univ

theorem M5.TupleCharacter.tuple_character_power : ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (∑ a : Fin n, M5.Character.value lam (f a)) ^ k := by
  change ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (∑ a : Fin n, M5.Character.value lam (f a)) ^ k
  intro D n k f lam
  classical
  simp only [M5.TupleCharacter.character_tuple_sum]
  exact (Fintype.sum_pow (fun a : Fin n => M5.Character.value lam (f a)) k).symm

theorem M5.TupleCharacter.ordered_tuple_power_count : ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * (∑ a : Fin n, M5.Character.value lam (f a)) ^ k) = (2 : ℤ) ^ D * (M5.TupleCharacter.count k f z : ℤ) := by
  classical
  change ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * (∑ a : Fin n, M5.Character.value lam (f a)) ^ k) = (2 : ℤ) ^ D * (M5.TupleCharacter.count k f z : ℤ)
  intro D n k f z
  simpa only [M5.TupleCharacter.tuple_character_power] using M5.TupleCharacter.tuple_character_count D n k f z

theorem M5.FiniteExclusion.alternating_subsets : ∀ S : Finset M5.BinaryPolynomial, (∑ H ∈ S.powerset, (-1 : ℤ)^H.card) = if S = ∅ then 1 else 0 := by
  classical
  change ∀ S : Finset M5.BinaryPolynomial, (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card) = if S = ∅ then 1 else 0
  intro S
  first
    | exact Finset.sum_powerset_neg_one_pow_card
    | exact Nat.sum_powerset_neg_one_pow_card

theorem M5.FiniteExclusion.filtered_powerset : ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), S.powerset.filter (fun H => ∀ p ∈ H, bad p = true) = (S.filter (fun p => bad p = true)).powerset := by
  change ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), S.powerset.filter (fun H => ∀ p ∈ H, bad p = true) = (S.filter (fun p => bad p = true)).powerset
  intro S bad
  classical
  apply Finset.ext
  intro H
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hHS, hbad⟩
    intro p hp
    exact Finset.mem_filter.mpr ⟨hHS hp, hbad p hp⟩
  · intro hH
    constructor
    · intro p hp
      exact (Finset.mem_filter.mp (hH hp)).1
    · intro p hp
      exact (Finset.mem_filter.mp (hH hp)).2

theorem M5.FiniteExclusion.exclusion_indicator : ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), M5.FiniteExclusion.exclusionSum S bad = if ∀ p ∈ S, bad p = false then 1 else 0 := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), M5.FiniteExclusion.exclusionSum S bad = if ∀ p ∈ S, bad p = false then 1 else 0
  intro S bad
  have he : S.filter (fun p => bad p = true) = ∅ ↔ ∀ p ∈ S, bad p = false := by
    constructor
    · intro h p hp
      have hn : bad p ≠ true := by
        intro hb
        have hm : p ∈ S.filter (fun p => bad p = true) :=
          Finset.mem_filter.mpr ⟨hp, hb⟩
        simpa [h] using hm
      cases hb : bad p <;> simp_all
    · intro h
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp
      simp [h p hp]
  calc
    M5.FiniteExclusion.exclusionSum S bad =
        ∑ H ∈ S.powerset.filter (fun H => ∀ p ∈ H, bad p = true), (-1 : ℤ) ^ H.card := by
      change (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card * (if ∀ p ∈ H, bad p = true then 1 else 0)) = _
      rw [Finset.sum_filter]
      simp only [mul_ite, mul_one, mul_zero]
    _ = ∑ H ∈ (S.filter (fun p => bad p = true)).powerset, (-1 : ℤ) ^ H.card := by
      rw [M5.FiniteExclusion.filtered_powerset]
    _ = if S.filter (fun p => bad p = true) = ∅ then 1 else 0 :=
      M5.FiniteExclusion.alternating_subsets _
    _ = if ∀ p ∈ S, bad p = false then 1 else 0 := by
      simpa only [he]

theorem M5.FactorProduct.common_factor_dvd : ∀ F H A : M5.BinaryPolynomial, F ≠ 0 → F ∣ A → (F * H ∣ A ↔ H ∣ A / F) := by
  change ∀ F H A : M5.BinaryPolynomial, F ≠ 0 → F ∣ A → (F * H ∣ A ↔ H ∣ A / F)
  intro F H A hF hFA
  constructor
  · intro h
    exact EuclideanDomain.dvd_div_of_mul_dvd h
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    calc
      A = F * (A / F) := (EuclideanDomain.mul_div_cancel' hF hFA).symm
      _ = F * (H * K) := congrArg (fun x => F * x) hK
      _ = (F * H) * K := (mul_assoc F H K).symm

theorem M5.FactorProduct.distinct_irreducibles_coprime : ∀ p q : M5.BinaryPolynomial, p.Monic → q.Monic → Irreducible p → Irreducible q → p ≠ q → IsCoprime p q := by
  change ∀ p q : M5.BinaryPolynomial, p.Monic → q.Monic → Irreducible p → Irreducible q → p ≠ q → IsCoprime p q
  intro p q hpm hqm hp hq hpq
  apply hp.coprime_iff_not_dvd.mpr
  rintro ⟨r, hr⟩
  rcases hq.isUnit_or_isUnit hr with hpu | hru
  · exact hp.not_isUnit hpu
  · rcases hru with ⟨u, hu⟩
    apply hpq
    apply Polynomial.eq_of_monic_of_associated hpm hqm
    exact ⟨u, by simpa only [hu] using hr.symm⟩

theorem M5.FactorProduct.irreducible_product_dvd : ∀ (S : Finset M5.BinaryPolynomial) (A : M5.BinaryPolynomial), (∀ p ∈ S, p.Monic ∧ Irreducible p) → ((∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, p ∣ A) := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (A : M5.BinaryPolynomial), (∀ p ∈ S, p.Monic ∧ Irreducible p) → ((∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, p ∣ A)
  intro S A hS
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun q : M5.BinaryPolynomial => q) hp).trans h
  · intro h
    refine Finset.prod_dvd_of_coprime ?_ h
    intro p hp q hq hpq
    exact M5.FactorProduct.distinct_irreducibles_coprime p q
      (hS p hp).1 (hS q hq).1 (hS p hp).2 (hS q hq).2 hpq

theorem M5.FactorProduct.cyclic_cap : ∀ (S : Finset M5.BinaryPolynomial) (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → S ⊆ M5.FactorProduct.residualFactors (M5.cyclicModulus N) F → F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → S ⊆ M5.FactorProduct.residualFactors (M5.cyclicModulus N) F → F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N
  intro S F N hN hF hFdvd hS
  have hmem : ∀ p ∈ S, p ∈ UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F) := by
    intro p hp
    simpa [M5.FactorProduct.residualFactors] using hS hp
  have hprops : ∀ p ∈ S, p.Monic ∧ Irreducible p := by
    intro p hp
    have hi := UniqueFactorizationMonoid.irreducible_of_normalized_factor p (hmem p hp)
    refine ⟨?_, hi⟩
    apply M5.Signature.binary_monic
    exact hi.ne_zero
  apply (M5.FactorProduct.common_factor_dvd F (∏ p ∈ S, p) (M5.cyclicModulus N) hF.ne_zero hFdvd).mpr
  apply (M5.FactorProduct.irreducible_product_dvd S (M5.cyclicModulus N / F) hprops).mpr
  intro p hp
  exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (hmem p hp)

theorem M5.FactorProduct.product_event_iff : ∀ (S : Finset M5.BinaryPolynomial) (F A : M5.BinaryPolynomial), F ≠ 0 → F ∣ A → (∀ p ∈ S, p.Monic ∧ Irreducible p) → (F * (∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, F * p ∣ A) := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (F A : M5.BinaryPolynomial), F ≠ 0 → F ∣ A → (∀ p ∈ S, p.Monic ∧ Irreducible p) → (F * (∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, F * p ∣ A)
  intro S F A hF hFA hS
  rw [M5.FactorProduct.common_factor_dvd F (∏ p ∈ S, p) A hF hFA,
    M5.FactorProduct.irreducible_product_dvd S (A / F) hS]
  constructor
  · intro h p hp
    exact (M5.FactorProduct.common_factor_dvd F p A hF hFA).mpr (h p hp)
  · intro h p hp
    exact (M5.FactorProduct.common_factor_dvd F p A hF hFA).mp (h p hp)

#print axioms M5.cutoff_gt_period
#print axioms M5.packed_range
#print axioms M5.packed_residue
#print axioms M5.progression_period
#print axioms M5.recovery_inclusion_positive
#print axioms M5.repair_above_packing
#print axioms M5.source_below_birth_bound
#print axioms M5.packed_injective
#print axioms M5.repair_no_collision
#print axioms M5.Lift.bounded_progression
#print axioms M5.Lift.cyclic_as_sub
#print axioms M5.Lift.bounded_source_order
#print axioms M5.Lift.modulus_multiple
#print axioms M5.Lift.progression_difference
#print axioms M5.Lift.progression_congruence
#print axioms M5.Lift.common_divisors_lift
#print axioms M5.Lift.triple_divisors_lift
#print axioms M5.Period.cyclic_dvd_iff_root_pow
#print axioms M5.Period.quotient_finite
#print axioms M5.Period.root_is_unit
#print axioms M5.Period.period_law
#print axioms M5.Period.period_dvd_of_dvd
#print axioms M5.Period.period_one
#print axioms M5.Period.quotient_cardinality
#print axioms M5.Period.period_cardinality_bound
#print axioms M5.CRT.interval_representative
#print axioms M5.CRT.prime_crt_representative
#print axioms M5.CRT.safe_prime_residue
#print axioms M5.CRT.residues_force_coprime
#print axioms M5.CRT.bounded_connectivity_repair
#print axioms M5.Packing.equal_residue_tag_strict
#print axioms M5.Packing.packed_support_anchor
#print axioms M5.Packing.packed_value_mod
#print axioms M5.Packing.tag_lt_weight
#print axioms M5.Packing.packed_support_range
#print axioms M5.Packing.packed_value_injective
#print axioms M5.Packing.packed_support_card
#print axioms M5.Character.bit_add
#print axioms M5.Character.bit_orthogonality
#print axioms M5.Character.character_add
#print axioms M5.Character.character_orthogonality
#print axioms M5.Character.finite_fibre_count
#print axioms M5.SupportPolynomial.packed_sum_image
#print axioms M5.SupportPolynomial.quotient_monomial_period
#print axioms M5.SupportPolynomial.support_coeff_zero
#print axioms M5.SupportPolynomial.support_degree_bound
#print axioms M5.SupportPolynomial.anchored_support_nonzero
#print axioms M5.SupportPolynomial.packed_polynomial_residue
#print axioms M5.Connectivity.divisor_moebius
#print axioms M5.Connectivity.support_gcd_dvd
#print axioms M5.Connectivity.support_divisor_filter
#print axioms M5.Connectivity.connected_indicator
#print axioms M5.RepairSupport.replacement_anchor
#print axioms M5.RepairSupport.replacement_card
#print axioms M5.RepairSupport.replacement_combined_gcd
#print axioms M5.RepairSupport.replacement_polynomial_residue
#print axioms M5.RepairSupport.replacement_range
#print axioms M5.RepairSupport.replacement_connected
#print axioms M5.Binomial.negative_coeff
#print axioms M5.Binomial.signed_product_split
#print axioms M5.Binomial.binomial_convolution
#print axioms M5.Binomial.signed_coefficient_eval
#print axioms M5.Signature.binary_monic
#print axioms M5.Signature.divisor_constant_one
#print axioms M5.Signature.binary_dvd_antisymm
#print axioms M5.Signature.ordinary_gcd_properties
#print axioms M5.Signature.exact_signature_lift
#print axioms M5.Signature.ordinary_gcd_period_bound
#print axioms M5.QuotientCharacter.character_add
#print axioms M5.QuotientCharacter.coordinates_zero_iff
#print axioms M5.QuotientCharacter.finite_fibre_count
#print axioms M5.QuotientCharacter.character_orthogonality
#print axioms M5.SubsetCharacter.value_zero
#print axioms M5.SubsetCharacter.character_subset_sum
#print axioms M5.SubsetCharacter.signed_product_expansion
#print axioms M5.SubsetCharacter.signed_product_coefficient
#print axioms M5.SubsetCharacter.subset_character_count
#print axioms M5.TupleCharacter.tuple_character_count
#print axioms M5.TupleCharacter.value_zero
#print axioms M5.TupleCharacter.character_tuple_sum
#print axioms M5.TupleCharacter.tuple_character_power
#print axioms M5.TupleCharacter.ordered_tuple_power_count
#print axioms M5.FiniteExclusion.alternating_subsets
#print axioms M5.FiniteExclusion.filtered_powerset
#print axioms M5.FiniteExclusion.exclusion_indicator
#print axioms M5.FactorProduct.common_factor_dvd
#print axioms M5.FactorProduct.distinct_irreducibles_coprime
#print axioms M5.FactorProduct.irreducible_product_dvd
#print axioms M5.FactorProduct.cyclic_cap
#print axioms M5.FactorProduct.product_event_iff
