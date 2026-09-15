import M5Checkpoint72

example : ∀ (w T : ℕ), 2 ≤ w → 0 < T → T < M5.packingCutoff w T := M5.cutoff_gt_period

#print axioms M5.cutoff_gt_period

example : ∀ (w T r j : ℕ), r < T → j < w → M5.packedExponent T r j < w * T := M5.packed_range

#print axioms M5.packed_range

example : ∀ (T r j : ℕ), r < T → M5.packedExponent T r j % T = r := M5.packed_residue

#print axioms M5.packed_residue

example : ∀ (T E j : ℕ), T ∣ E → T ∣ T + j * E := M5.progression_period

#print axioms M5.progression_period

example : ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included := M5.recovery_inclusion_positive

#print axioms M5.recovery_inclusion_positive

example : ∀ (w T e k : ℕ), 0 < T → w ≤ k → w * T ≤ e + k * T := M5.repair_above_packing

#print axioms M5.repair_above_packing

example : ∀ (w T E N : ℕ), N < M5.packingCutoff w T + E → E ≤ 2 ^ (w * T) → N < M5.birthBound w T := M5.source_below_birth_bound

#print axioms M5.source_below_birth_bound

example : ∀ (T r s j k : ℕ), r < T → s < T → M5.packedExponent T r j = M5.packedExponent T s k → r = s ∧ j = k := M5.packed_injective

#print axioms M5.packed_injective

example : ∀ (w T r j e k : ℕ), r < T → j < w → w ≤ k → M5.packedExponent T r j ≠ e + k * T := M5.repair_no_collision

#print axioms M5.repair_no_collision

example : ∀ T E L : ℕ, 0 < E → T < L → ∃ j : ℕ, L ≤ T + j * E ∧ T + j * E < L + E := M5.Lift.bounded_progression

#print axioms M5.Lift.bounded_progression

example : ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1 := M5.Lift.cyclic_as_sub

#print axioms M5.Lift.cyclic_as_sub

example : ∀ w T E : ℕ, 2 ≤ w → 0 < T → 0 < E → E ≤ 2 ^ (w * T) → ∃ j : ℕ, M5.packingCutoff w T ≤ T + j * E ∧ T + j * E < M5.birthBound w T := M5.Lift.bounded_source_order

#print axioms M5.Lift.bounded_source_order

example : ∀ E N : ℕ, E ∣ N → M5.cyclicModulus E ∣ M5.cyclicModulus N := M5.Lift.modulus_multiple

#print axioms M5.Lift.modulus_multiple

example : ∀ T E j : ℕ, M5.cyclicModulus (T + j * E) - M5.cyclicModulus T = (Polynomial.X : M5.BinaryPolynomial) ^ T * M5.cyclicModulus (j * E) := M5.Lift.progression_difference

#print axioms M5.Lift.progression_difference

example : ∀ (G : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → G ∣ M5.cyclicModulus (T + j * E) - M5.cyclicModulus T := M5.Lift.progression_congruence

#print axioms M5.Lift.progression_congruence

example : ∀ (G D : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → D ∣ G → (D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T) := M5.Lift.common_divisors_lift

#print axioms M5.Lift.common_divisors_lift

example : ∀ (a b D : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → ((D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus (T + j * E)) ↔ (D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus T)) := M5.Lift.triple_divisors_lift

#print axioms M5.Lift.triple_divisors_lift

example : ∀ (F : M5.BinaryPolynomial) (N : ℕ), F ∣ M5.cyclicModulus N ↔ (AdjoinRoot.root F) ^ N = 1 := M5.Period.cyclic_dvd_iff_root_pow

#print axioms M5.Period.cyclic_dvd_iff_root_pow

example : ∀ (F : M5.BinaryPolynomial), F.Monic → Finite (AdjoinRoot F) := M5.Period.quotient_finite

#print axioms M5.Period.quotient_finite

example : ∀ (F : M5.BinaryPolynomial), F.coeff 0 = 1 → IsUnit (AdjoinRoot.root F) := M5.Period.root_is_unit

#print axioms M5.Period.root_is_unit

example : ∀ (F : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → 0 < M5.signaturePeriod F ∧ ∀ N : ℕ, F ∣ M5.cyclicModulus N ↔ M5.signaturePeriod F ∣ N := M5.Period.period_law

#print axioms M5.Period.period_law

example : ∀ (F G : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → G.Monic → G.coeff 0 = 1 → F ∣ G → M5.signaturePeriod F ∣ M5.signaturePeriod G := M5.Period.period_dvd_of_dvd

#print axioms M5.Period.period_dvd_of_dvd

example : M5.signaturePeriod (1 : M5.BinaryPolynomial) = 1 := M5.Period.period_one

#print axioms M5.Period.period_one

example : ∀ F : M5.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree := M5.Period.quotient_cardinality

#print axioms M5.Period.quotient_cardinality

example : ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.signaturePeriod F ≤ 2 ^ F.natDegree := M5.Period.period_cardinality_bound

#print axioms M5.Period.period_cardinality_bound

example : ∀ R r w : ℕ, 0 < R → ∃ k : ℕ, w ≤ k ∧ k < w + R ∧ Nat.ModEq R k r := M5.CRT.interval_representative

#print axioms M5.CRT.interval_representative

example : ∀ δ e : ℕ, 0 < δ → ∃ r : ℕ, r < M5.CRT.primeProduct δ ∧ ∀ p ∈ δ.primeFactors, Nat.ModEq p r (M5.CRT.repairResidue e p) := M5.CRT.prime_crt_representative

#print axioms M5.CRT.prime_crt_representative

example : ∀ p δ T e : ℕ, p.Prime → p ∣ δ → Nat.gcd (Nat.gcd T δ) e = 1 → ¬ p ∣ e + M5.CRT.repairResidue e p * T := M5.CRT.safe_prime_residue

#print axioms M5.CRT.safe_prime_residue

example : ∀ δ T e k : ℕ, 0 < δ → Nat.gcd (Nat.gcd T δ) e = 1 → (∀ p ∈ δ.primeFactors, Nat.ModEq p k (M5.CRT.repairResidue e p)) → Nat.gcd δ (e + k * T) = 1 := M5.CRT.residues_force_coprime

#print axioms M5.CRT.residues_force_coprime

example : ∀ δ T e w : ℕ, 0 < δ → 0 < T → Nat.gcd (Nat.gcd T δ) e = 1 → ∃ k : ℕ, w ≤ k ∧ k < w + δ ∧ Nat.gcd δ (e + k * T) = 1 := M5.CRT.bounded_connectivity_repair

#print axioms M5.CRT.bounded_connectivity_repair

example : ∀ (w T : ℕ) (r : Fin w → Fin T) (i j : Fin w), i < j → r i = r j → M5.Packing.occurrenceTag r i < M5.Packing.occurrenceTag r j := M5.Packing.equal_residue_tag_strict

#print axioms M5.Packing.equal_residue_tag_strict

example : ∀ (w T : ℕ) (r : Fin w → Fin T) (hw : 0 < w), (r ⟨0, hw⟩).val = 0 → 0 ∈ M5.Packing.packedSupport r := M5.Packing.packed_support_anchor

#print axioms M5.Packing.packed_support_anchor

example : ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.packedValue r i % T = (r i).val := M5.Packing.packed_value_mod

#print axioms M5.Packing.packed_value_mod

example : ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.occurrenceTag r i < w := M5.Packing.tag_lt_weight

#print axioms M5.Packing.tag_lt_weight

example : ∀ (w T : ℕ) (r : Fin w → Fin T) (e : ℕ), e ∈ M5.Packing.packedSupport r → e < w * T := M5.Packing.packed_support_range

#print axioms M5.Packing.packed_support_range

example : ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) := M5.Packing.packed_value_injective

#print axioms M5.Packing.packed_value_injective

example : ∀ (w T : ℕ) (r : Fin w → Fin T), (M5.Packing.packedSupport r).card = w := M5.Packing.packed_support_card

#print axioms M5.Packing.packed_support_card

example : ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c := M5.Character.bit_add

#print axioms M5.Character.bit_add

example : ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0 := M5.Character.bit_orthogonality

#print axioms M5.Character.bit_orthogonality

example : ∀ (D : ℕ) (lam z u : M5.Character.BinaryVector D), M5.Character.value lam (z + u) = M5.Character.value lam z * M5.Character.value lam u := M5.Character.character_add

#print axioms M5.Character.character_add

example : ∀ (D : ℕ) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z) = if z = 0 then (2 : ℤ) ^ D else 0 := M5.Character.character_orthogonality

#print axioms M5.Character.character_orthogonality

example : ∀ (D n : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ u : Fin n, M5.Character.value lam (f u)) = (2 : ℤ) ^ D * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ) := M5.Character.finite_fibre_count

#print axioms M5.Character.finite_fibre_count

example : ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) → M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r) = ∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ M5.Packing.packedValue r i := M5.SupportPolynomial.packed_sum_image

#print axioms M5.SupportPolynomial.packed_sum_image

example : ∀ T a j : ℕ, AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) = AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ a) := M5.SupportPolynomial.quotient_monomial_period

#print axioms M5.SupportPolynomial.quotient_monomial_period

example : ∀ S : Finset ℕ, (M5.SupportPolynomial.ofSupport S).coeff 0 = if 0 ∈ S then 1 else 0 := M5.SupportPolynomial.support_coeff_zero

#print axioms M5.SupportPolynomial.support_coeff_zero

example : ∀ (S : Finset ℕ) (K : ℕ), 0 < K → (∀ e ∈ S, e < K) → (M5.SupportPolynomial.ofSupport S).natDegree < K := M5.SupportPolynomial.support_degree_bound

#print axioms M5.SupportPolynomial.support_degree_bound

example : ∀ S : Finset ℕ, 0 ∈ S → M5.SupportPolynomial.ofSupport S ≠ 0 := M5.SupportPolynomial.anchored_support_nonzero

#print axioms M5.SupportPolynomial.anchored_support_nonzero

example : ∀ (w T : ℕ) (r : Fin w → Fin T), AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r)) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofResidueTuple r) := M5.SupportPolynomial.packed_polynomial_residue

#print axioms M5.SupportPolynomial.packed_polynomial_residue

example : ∀ n : ℕ, (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0 := M5.Connectivity.divisor_moebius

#print axioms M5.Connectivity.divisor_moebius

example : ∀ (N d : ℕ) (A B : Finset ℕ), d ∣ M5.Connectivity.supportGcd N A B ↔ d ∣ N ∧ (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) := M5.Connectivity.support_gcd_dvd

#print axioms M5.Connectivity.support_gcd_dvd

example : ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → N.divisors.filter (fun d => (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b)) = (M5.Connectivity.supportGcd N A B).divisors := M5.Connectivity.support_divisor_filter

#print axioms M5.Connectivity.support_divisor_filter

example : ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → (∑ d ∈ N.divisors, if (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) then ArithmeticFunction.moebius d else 0) = if M5.Connectivity.supportGcd N A B = 1 then (1 : ℤ) else 0 := M5.Connectivity.connected_indicator

#print axioms M5.Connectivity.connected_indicator

example : ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q := M5.RepairSupport.replacement_anchor

#print axioms M5.RepairSupport.replacement_anchor

example : ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card := M5.RepairSupport.replacement_card

#print axioms M5.RepairSupport.replacement_card

example : ∀ (A B : Finset ℕ) (e q : ℕ), M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) := M5.RepairSupport.replacement_combined_gcd

#print axioms M5.RepairSupport.replacement_combined_gcd

example : ∀ (A : Finset ℕ) (e k T : ℕ), e ∈ A → e + k * T ∉ A → AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.RepairSupport.repaired A e (e + k * T))) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport A) := M5.RepairSupport.replacement_polynomial_residue

#print axioms M5.RepairSupport.replacement_polynomial_residue

example : ∀ (A : Finset ℕ) (e q L : ℕ), (∀ a ∈ A, a < L) → q < L → ∀ a ∈ M5.RepairSupport.repaired A e q, a < L := M5.RepairSupport.replacement_range

#print axioms M5.RepairSupport.replacement_range

example : ∀ (A B : Finset ℕ) (e q : ℕ), Nat.gcd (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) q = 1 → M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = 1 := M5.RepairSupport.replacement_connected

#print axioms M5.RepairSupport.replacement_connected

example : ∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ) := M5.Binomial.negative_coeff

#print axioms M5.Binomial.negative_coeff

example : ∀ (S : Finset ℕ) (f : ℕ → ℤ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → M5.Binomial.signedProduct S f = (1 - Polynomial.X) ^ M5.Binomial.negativeCount S f * (1 + Polynomial.X) ^ (S.card - M5.Binomial.negativeCount S f) := M5.Binomial.signed_product_split

#print axioms M5.Binomial.signed_product_split

example : ∀ m n k : ℕ, (((1 - Polynomial.X : Polynomial ℤ) ^ m) * (1 + Polynomial.X) ^ n).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * (n.choose (k-j) : ℤ) := M5.Binomial.binomial_convolution

#print axioms M5.Binomial.binomial_convolution

example : ∀ (S : Finset ℕ) (f : ℕ → ℤ) (k : ℕ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → (M5.Binomial.signedProduct S f).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ((M5.Binomial.negativeCount S f).choose j : ℤ) * ((S.card - M5.Binomial.negativeCount S f).choose (k-j) : ℤ) := M5.Binomial.signed_coefficient_eval

#print axioms M5.Binomial.signed_coefficient_eval

example : ∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic := M5.Signature.binary_monic

#print axioms M5.Signature.binary_monic

example : ∀ P a : M5.BinaryPolynomial, P ∣ a → a.coeff 0 = 1 → P.coeff 0 = 1 := M5.Signature.divisor_constant_one

#print axioms M5.Signature.divisor_constant_one

example : ∀ P Q : M5.BinaryPolynomial, P ∣ Q → Q ∣ P → P = Q := M5.Signature.binary_dvd_antisymm

#print axioms M5.Signature.binary_dvd_antisymm

example : ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → (EuclideanDomain.gcd a b).Monic ∧ (EuclideanDomain.gcd a b).coeff 0 = 1 ∧ (EuclideanDomain.gcd a b).natDegree ≤ b.natDegree := M5.Signature.ordinary_gcd_properties

#print axioms M5.Signature.ordinary_gcd_properties

example : ∀ (a b : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → M5.completeSignature a b (T+j*E) = M5.completeSignature a b T := M5.Signature.exact_signature_lift

#print axioms M5.Signature.exact_signature_lift

example : ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → 0 < M5.signaturePeriod (EuclideanDomain.gcd a b) ∧ M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ b.natDegree := M5.Signature.ordinary_gcd_period_bound

#print axioms M5.Signature.ordinary_gcd_period_bound

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z u : AdjoinRoot P), M5.QuotientCharacter.value P hP lam (z + u) = M5.QuotientCharacter.value P hP lam z * M5.QuotientCharacter.value P hP lam u := M5.QuotientCharacter.character_add

#print axioms M5.QuotientCharacter.character_add

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), M5.QuotientCharacter.coordinates P hP z = 0 ↔ z = 0 := M5.QuotientCharacter.coordinates_zero_iff

#print axioms M5.QuotientCharacter.coordinates_zero_iff

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (n : ℕ) (f : Fin n → AdjoinRoot P) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z * ∑ u : Fin n, M5.QuotientCharacter.value P hP lam (f u)) = (2 : ℤ) ^ P.natDegree * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ) := M5.QuotientCharacter.finite_fibre_count

#print axioms M5.QuotientCharacter.finite_fibre_count

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z) = if z = 0 then (2 : ℤ) ^ P.natDegree else 0 := M5.QuotientCharacter.character_orthogonality

#print axioms M5.QuotientCharacter.character_orthogonality
