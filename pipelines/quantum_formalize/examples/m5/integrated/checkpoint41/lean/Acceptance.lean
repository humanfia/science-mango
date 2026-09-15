import M5Accepted

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

example : ∀ n : ℕ, (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0 := M5.Connectivity.divisor_moebius

#print axioms M5.Connectivity.divisor_moebius

example : ∀ (N d : ℕ) (A B : Finset ℕ), d ∣ M5.Connectivity.supportGcd N A B ↔ d ∣ N ∧ (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) := M5.Connectivity.support_gcd_dvd

#print axioms M5.Connectivity.support_gcd_dvd

example : ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → N.divisors.filter (fun d => (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b)) = (M5.Connectivity.supportGcd N A B).divisors := M5.Connectivity.support_divisor_filter

#print axioms M5.Connectivity.support_divisor_filter

example : ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → (∑ d ∈ N.divisors, if (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) then ArithmeticFunction.moebius d else 0) = if M5.Connectivity.supportGcd N A B = 1 then (1 : ℤ) else 0 := M5.Connectivity.connected_indicator

#print axioms M5.Connectivity.connected_indicator
