import M5Accepted
import M5Binomial
import M5CRT
import M5Cardinality
import M5Character
import M5Foundation
import M5IntegerMobius
import M5Lift
import M5Packing
import M5PackingInjective
import M5Period
import M5QuotientCharacter
import M5QuotientFinite
import M5RepairSupport
import M5Signature
import M5StageOne
import M5SupportPolynomial

theorem M5.RepairSupport.replacement_anchor : ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q
  intro A e q he h0
  simp [M5.RepairSupport.repaired, he, Ne.symm he, h0]

theorem M5.RepairSupport.replacement_card : ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card
  intro A e q he hq
  change (insert q (A.erase e)).card = A.card
  have hq' : q ∉ A.erase e := fun h => hq (Finset.mem_erase.mp h).2
  rw [Finset.card_insert_of_notMem hq', Finset.card_erase_of_mem he]
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨e, he⟩
  omega

theorem M5.RepairSupport.replacement_combined_gcd : ∀ (A B : Finset ℕ) (e q : ℕ), M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) := by
  intro A B e q
  unfold M5.RepairSupport.combinedGcd M5.RepairSupport.repaired
  rw [Finset.gcd_insert]
  change Nat.gcd (Nat.gcd q ((A.erase e).gcd id)) (B.gcd id) = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id))
  exact Nat.gcd_assoc q ((A.erase e).gcd id) (B.gcd id)

theorem M5.RepairSupport.replacement_polynomial_residue : ∀ (A : Finset ℕ) (e k T : ℕ), e ∈ A → e + k * T ∉ A → AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.RepairSupport.repaired A e (e + k * T))) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport A) := by
  intro A e k T he hf
  classical
  have hf' : e + k * T ∉ A.erase e := by
    intro h
    exact hf (Finset.mem_of_mem_erase h)
  unfold M5.RepairSupport.repaired M5.SupportPolynomial.ofSupport
  rw [Finset.sum_insert hf']
  conv_rhs =>
    rw [← Finset.insert_erase he, Finset.sum_insert (Finset.notMem_erase e A)]
  rw [map_add, map_add]
  congr 1
  first
  | apply M5.quotient_monomial_period
  | apply M5.SupportPolynomial.quotient_monomial_period
  | simpa only [Polynomial.monomial_one] using
      (M5.quotient_monomial_period (T := T) (a := e) (j := k))

theorem M5.RepairSupport.replacement_range : ∀ (A : Finset ℕ) (e q L : ℕ), (∀ a ∈ A, a < L) → q < L → ∀ a ∈ M5.RepairSupport.repaired A e q, a < L := by
  change ∀ (A : Finset ℕ) (e q L : ℕ), (∀ a ∈ A, a < L) → q < L → ∀ a ∈ M5.RepairSupport.repaired A e q, a < L
  intro A e q L hA hq a ha
  change a ∈ insert q (A.erase e) at ha
  rcases Finset.mem_insert.mp ha with h | h
  · subst a
    exact hq
  · exact hA a (Finset.mem_of_mem_erase h)

theorem M5.RepairSupport.replacement_connected : ∀ (A B : Finset ℕ) (e q : ℕ), Nat.gcd (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) q = 1 → M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = 1 := by
  intro A B e q h
  rw [M5.RepairSupport.replacement_combined_gcd, Nat.gcd_comm q]
  exact h

theorem M5.Binomial.negative_coeff : ∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ) := by
  change ∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ)
  intro m j
  have h : (1 : Polynomial ℤ) - Polynomial.X =
      Polynomial.X * Polynomial.C (-1 : ℤ) + 1 := by
    simp
    <;> ring
  rw [h, add_pow, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, one_pow, mul_one, mul_pow,
    ← Polynomial.C_pow, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [Polynomial.coeff_X_pow, hij, hij.symm]
  · intro hj
    have hmj : m < j := by
      simp only [Finset.mem_range] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hmj]

theorem M5.Binomial.signed_product_split : ∀ (S : Finset ℕ) (f : ℕ → ℤ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → M5.Binomial.signedProduct S f = (1 - Polynomial.X) ^ M5.Binomial.negativeCount S f * (1 + Polynomial.X) ^ (S.card - M5.Binomial.negativeCount S f) := by
  classical
  intro S f hf
  unfold M5.Binomial.signedProduct M5.Binomial.negativeCount
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun s => f s = -1)]
  have hn : (S.filter (fun s => f s = -1)).prod
      (fun s => (1 + Polynomial.C (f s) * Polynomial.X : Polynomial ℤ)) =
      (1 - Polynomial.X : Polynomial ℤ) ^ (S.filter (fun s => f s = -1)).card := by
    calc
      _ = (S.filter (fun s => f s = -1)).prod
          (fun _ => (1 - Polynomial.X : Polynomial ℤ)) := by
        apply Finset.prod_congr rfl
        intro s hs
        have h := (Finset.mem_filter.mp hs).2
        simp [h, sub_eq_add_neg]
      _ = _ := by simp
  have hp : (S.filter (fun s => ¬ f s = -1)).prod
      (fun s => (1 + Polynomial.C (f s) * Polynomial.X : Polynomial ℤ)) =
      (1 + Polynomial.X : Polynomial ℤ) ^ (S.filter (fun s => ¬ f s = -1)).card := by
    calc
      _ = (S.filter (fun s => ¬ f s = -1)).prod
          (fun _ => (1 + Polynomial.X : Polynomial ℤ)) := by
        apply Finset.prod_congr rfl
        intro s hs
        obtain ⟨hs, hneg⟩ := Finset.mem_filter.mp hs
        have hpos : f s = 1 := (hf s hs).resolve_right hneg
        simp [hpos]
      _ = _ := by simp
  rw [hn, hp]
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun s => f s = -1)
  have hc : (S.filter (fun s => ¬ f s = -1)).card =
      S.card - (S.filter (fun s => f s = -1)).card := by omega
  rw [hc]

theorem M5.Binomial.binomial_convolution : ∀ m n k : ℕ, (((1 - Polynomial.X : Polynomial ℤ) ^ m) * (1 + Polynomial.X) ^ n).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * (n.choose (k-j) : ℤ) := by
  change ∀ m n k : ℕ, (((1 - Polynomial.X : Polynomial ℤ) ^ m) * (1 + Polynomial.X) ^ n).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * (n.choose (k - j) : ℤ)
  intro m n k
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [M5.Binomial.negative_coeff, Polynomial.coeff_one_add_X_pow]

theorem M5.Binomial.signed_coefficient_eval : ∀ (S : Finset ℕ) (f : ℕ → ℤ) (k : ℕ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → (M5.Binomial.signedProduct S f).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ((M5.Binomial.negativeCount S f).choose j : ℤ) * ((S.card - M5.Binomial.negativeCount S f).choose (k-j) : ℤ) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (S : Finset ℕ) (f : ℕ → ℤ) (k : ℕ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → (M5.Binomial.signedProduct S f).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ((M5.Binomial.negativeCount S f).choose j : ℤ) * ((S.card - M5.Binomial.negativeCount S f).choose (k-j) : ℤ)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro S f k hf
  rw [M5.Binomial.signed_product_split S f hf]
  exact M5.Binomial.binomial_convolution (M5.Binomial.negativeCount S f) (S.card - M5.Binomial.negativeCount S f) k

theorem M5.Signature.binary_monic : ∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic := by
  change ∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic
  intro P hP
  have h : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  change P.leadingCoeff = 1
  exact h P.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hP)

theorem M5.Signature.divisor_constant_one : ∀ P a : M5.BinaryPolynomial, P ∣ a → a.coeff 0 = 1 → P.coeff 0 = 1 := by
  change ∀ P a : M5.BinaryPolynomial, P ∣ a → a.coeff 0 = 1 → P.coeff 0 = 1
  intro P a hdiv ha
  obtain ⟨q, rfl⟩ := hdiv
  rw [Polynomial.mul_coeff_zero] at ha
  have h : ∀ c d : ZMod 2, c * d = 1 → c = 1 := by decide
  exact h (P.coeff 0) (q.coeff 0) ha

theorem M5.Signature.binary_dvd_antisymm : ∀ P Q : M5.BinaryPolynomial, P ∣ Q → Q ∣ P → P = Q := by
  change ∀ P Q : M5.BinaryPolynomial, P ∣ Q → Q ∣ P → P = Q
  intro P Q hPQ hQP
  by_cases hP : P = 0
  · subst P
    exact (zero_dvd_iff.mp hPQ).symm
  by_cases hQ : Q = 0
  · subst Q
    exact zero_dvd_iff.mp hQP
  exact Polynomial.eq_of_monic_of_associated
    (M5.Signature.binary_monic P hP)
    (M5.Signature.binary_monic Q hQ)
    (associated_of_dvd_dvd hPQ hQP)

theorem M5.Signature.ordinary_gcd_properties : ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → (EuclideanDomain.gcd a b).Monic ∧ (EuclideanDomain.gcd a b).coeff 0 = 1 ∧ (EuclideanDomain.gcd a b).natDegree ≤ b.natDegree := by
  change ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → (EuclideanDomain.gcd a b).Monic ∧ (EuclideanDomain.gcd a b).coeff 0 = 1 ∧ (EuclideanDomain.gcd a b).natDegree ≤ b.natDegree
  intro a b ha hb
  have hc : (EuclideanDomain.gcd a b).coeff 0 = 1 :=
    M5.Signature.divisor_constant_one _ a (EuclideanDomain.gcd_dvd_left a b) ha
  have hg : EuclideanDomain.gcd a b ≠ 0 := by
    intro h
    simp [h] at hc
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  exact ⟨M5.Signature.binary_monic _ hg, hc,
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right a b) hb0⟩

theorem M5.Signature.exact_signature_lift : ∀ (a b : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → M5.completeSignature a b (T+j*E) = M5.completeSignature a b T := by
  change ∀ (a b : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → M5.completeSignature a b (T+j*E) = M5.completeSignature a b T
  intro a b T E j hE
  unfold M5.completeSignature
  have lift (D : M5.BinaryPolynomial) (hD : D ∣ EuclideanDomain.gcd a b) :
      D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T := by
    first
    | apply M5.Lift.common_divisors_lift <;> assumption
    | symm; apply M5.Lift.common_divisors_lift <;> assumption
  apply M5.Signature.binary_dvd_antisymm
  · apply EuclideanDomain.dvd_gcd
    · exact EuclideanDomain.gcd_dvd_left _ _
    · exact (lift _ (EuclideanDomain.gcd_dvd_left _ _)).mp (EuclideanDomain.gcd_dvd_right _ _)
  · apply EuclideanDomain.dvd_gcd
    · exact EuclideanDomain.gcd_dvd_left _ _
    · exact (lift _ (EuclideanDomain.gcd_dvd_left _ _)).mpr (EuclideanDomain.gcd_dvd_right _ _)

theorem M5.Signature.ordinary_gcd_period_bound : ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → 0 < M5.signaturePeriod (EuclideanDomain.gcd a b) ∧ M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ b.natDegree := by
  change ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → 0 < M5.signaturePeriod (EuclideanDomain.gcd a b) ∧ M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ b.natDegree
  intro a b ha hb
  obtain ⟨hm, hc, hd⟩ := M5.Signature.ordinary_gcd_properties a b ha hb
  have hl := M5.Period.period_law (EuclideanDomain.gcd a b) hm hc
  have hbound := M5.Period.period_cardinality_bound (EuclideanDomain.gcd a b) hm hc
  refine ⟨hl.1, hbound.trans ?_⟩
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hd

theorem M5.QuotientCharacter.character_add : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z u : AdjoinRoot P), M5.QuotientCharacter.value P hP lam (z + u) = M5.QuotientCharacter.value P hP lam z * M5.QuotientCharacter.value P hP lam u := by
  intro P hP lam z u
  unfold M5.QuotientCharacter.value
  simp only [map_add, M5.Character.character_add]

theorem M5.QuotientCharacter.coordinates_zero_iff : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), M5.QuotientCharacter.coordinates P hP z = 0 ↔ z = 0 := by
  intro P hP z
  first
  | exact (M5.QuotientCharacter.coordinates P hP).map_eq_zero_iff
  | simp [M5.QuotientCharacter.coordinates]

theorem M5.QuotientCharacter.finite_fibre_count : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (n : ℕ) (f : Fin n → AdjoinRoot P) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z * ∑ u : Fin n, M5.QuotientCharacter.value P hP lam (f u)) = (2 : ℤ) ^ P.natDegree * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ) := by
  classical
  intro P hP n f z
  have hfilter :
      (Finset.univ.filter (fun u : Fin n =>
        M5.QuotientCharacter.coordinates P hP (f u) =
          M5.QuotientCharacter.coordinates P hP z)) =
      (Finset.univ.filter (fun u : Fin n => f u = z)) := by
    apply Finset.filter_congr
    intro u hu
    exact (M5.QuotientCharacter.coordinates P hP).injective.eq_iff
  rw [← hfilter]
  unfold M5.QuotientCharacter.value
  apply M5.Character.finite_fibre_count

theorem M5.QuotientCharacter.character_orthogonality : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z) = if z = 0 then (2 : ℤ) ^ P.natDegree else 0 := by
  intro P hP z
  classical
  unfold M5.QuotientCharacter.value
  rw [M5.Character.character_orthogonality]
  simp only [M5.QuotientCharacter.coordinates_zero_iff]

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
