import M5CRT
import M5Cardinality
import M5Character
import M5Foundation
import M5IntegerMobius
import M5Lift
import M5Packing
import M5PackingInjective
import M5Period
import M5QuotientFinite
import M5StageOne
import M5SupportPolynomial

theorem M5.Lift.bounded_progression : ∀ T E L : ℕ, 0 < E → T < L → ∃ j : ℕ, L ≤ T + j * E ∧ T + j * E < L + E := by
  change ∀ T E L : ℕ, 0 < E → T < L → ∃ j : ℕ, L ≤ T + j * E ∧ T + j * E < L + E
  intro T E L hE hTL
  let a := L - T - 1
  have ha : T + a + 1 = L := by
    dsimp [a]
    omega
  have hdiv := Nat.mod_add_div a E
  have hmod := Nat.mod_lt a hE
  rw [Nat.mul_comm E (a / E)] at hdiv
  refine ⟨a / E + 1, ?_⟩
  rw [Nat.add_mul, Nat.one_mul]
  constructor <;> omega

theorem M5.Lift.cyclic_as_sub : ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1 := by
  change ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1
  intro N
  simp [M5.cyclicModulus, sub_eq_add_neg, CharTwo.neg_eq]

theorem M5.Lift.bounded_source_order : ∀ w T E : ℕ, 2 ≤ w → 0 < T → 0 < E → E ≤ 2 ^ (w * T) → ∃ j : ℕ, M5.packingCutoff w T ≤ T + j * E ∧ T + j * E < M5.birthBound w T := by
  change ∀ w T E : ℕ, 2 ≤ w → 0 < T → 0 < E → E ≤ 2 ^ (w * T) → ∃ j : ℕ, M5.packingCutoff w T ≤ T + j * E ∧ T + j * E < M5.birthBound w T
  intro w T E hw hT hE hbound
  have hcut : T < M5.packingCutoff w T := by
    apply M5.cutoff_gt_period <;> assumption
  obtain ⟨j, hjlo, hjhi⟩ := M5.Lift.bounded_progression T E (M5.packingCutoff w T) hE hcut
  refine ⟨j, hjlo, ?_⟩
  apply M5.source_below_birth_bound <;> omega

theorem M5.Lift.modulus_multiple : ∀ E N : ℕ, E ∣ N → M5.cyclicModulus E ∣ M5.cyclicModulus N := by
  change ∀ E N : ℕ, E ∣ N → M5.cyclicModulus E ∣ M5.cyclicModulus N
  intro E N h
  rcases h with ⟨k, rfl⟩
  rw [M5.Lift.cyclic_as_sub, M5.Lift.cyclic_as_sub, pow_mul]
  exact sub_one_dvd_pow_sub_one ((Polynomial.X : M5.BinaryPolynomial) ^ E) k

theorem M5.Lift.progression_difference : ∀ T E j : ℕ, M5.cyclicModulus (T + j * E) - M5.cyclicModulus T = (Polynomial.X : M5.BinaryPolynomial) ^ T * M5.cyclicModulus (j * E) := by
  change ∀ T E j : ℕ, M5.cyclicModulus (T + j * E) - M5.cyclicModulus T = (Polynomial.X : M5.BinaryPolynomial) ^ T * M5.cyclicModulus (j * E)
  intro T E j
  simp only [M5.Lift.cyclic_as_sub, pow_add]
  ring

theorem M5.Lift.progression_congruence : ∀ (G : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → G ∣ M5.cyclicModulus (T + j * E) - M5.cyclicModulus T := by
  change ∀ (G : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → G ∣ M5.cyclicModulus (T + j * E) - M5.cyclicModulus T
  intro G T E j h
  have hE : E ∣ j * E := ⟨j, Nat.mul_comm j E⟩
  have hG := dvd_trans h (M5.Lift.modulus_multiple E (j * E) hE)
  rw [M5.Lift.progression_difference]
  rcases hG with ⟨k, hk⟩
  refine ⟨(Polynomial.X : M5.BinaryPolynomial) ^ T * k, ?_⟩
  rw [hk]
  ring

theorem M5.Lift.common_divisors_lift : ∀ (G D : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → D ∣ G → (D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T) := by
  change ∀ (G D : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → D ∣ G → (D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T)
  intro G D T E j hG hD
  have hd : D ∣ M5.cyclicModulus (T + j * E) - M5.cyclicModulus T :=
    dvd_trans hD (M5.Lift.progression_congruence G T E j hG)
  constructor
  · intro h
    simpa only [sub_sub_cancel] using dvd_sub h hd
  · intro h
    simpa only [sub_add_cancel] using dvd_add hd h

theorem M5.Lift.triple_divisors_lift : ∀ (a b D : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → ((D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus (T + j * E)) ↔ (D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus T)) := by
  change ∀ (a b D : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → ((D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus (T + j * E)) ↔ (D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus T))
  intro a b D T E j hG
  constructor
  · rintro ⟨ha, hb, h⟩
    have hD : D ∣ EuclideanDomain.gcd a b := EuclideanDomain.dvd_gcd ha hb
    exact ⟨ha, hb, (M5.Lift.common_divisors_lift (EuclideanDomain.gcd a b) D T E j hG hD).mp h⟩
  · rintro ⟨ha, hb, h⟩
    have hD : D ∣ EuclideanDomain.gcd a b := EuclideanDomain.dvd_gcd ha hb
    exact ⟨ha, hb, (M5.Lift.common_divisors_lift (EuclideanDomain.gcd a b) D T E j hG hD).mpr h⟩

theorem M5.Period.cyclic_dvd_iff_root_pow : ∀ (F : M5.BinaryPolynomial) (N : ℕ), F ∣ M5.cyclicModulus N ↔ (AdjoinRoot.root F) ^ N = 1 := by
  change ∀ (F : M5.BinaryPolynomial) (N : ℕ), F ∣ M5.cyclicModulus N ↔ (AdjoinRoot.root F) ^ N = 1
  intro F N
  have hpoly : -(1 : M5.BinaryPolynomial) = 1 := CharTwo.neg_eq _
  have hroot : -(1 : AdjoinRoot F) = 1 := by
    simpa only [map_neg, map_one] using congrArg (AdjoinRoot.mk F) hpoly
  rw [← AdjoinRoot.mk_eq_zero]
  simp [M5.cyclicModulus, map_add, map_pow, AdjoinRoot.mk_X,
    add_eq_zero_iff_eq_neg, hroot]

theorem M5.Period.root_is_unit : ∀ (F : M5.BinaryPolynomial), F.coeff 0 = 1 → IsUnit (AdjoinRoot.root F) := by
  change ∀ (F : M5.BinaryPolynomial), F.coeff 0 = 1 → IsUnit (AdjoinRoot.root F)
  intro F hF
  have h : AdjoinRoot.root F * AdjoinRoot.mk F F.divX + 1 = 0 := by
    simpa only [map_add, map_mul, hF, Polynomial.C_1, map_one,
      AdjoinRoot.mk_self, AdjoinRoot.root] using
      congrArg (AdjoinRoot.mk F) (Polynomial.X_mul_divX_add F)
  have hinv : AdjoinRoot.root F * (-AdjoinRoot.mk F F.divX) = 1 := by
    rw [mul_neg, eq_neg_of_add_eq_zero_left h, neg_neg]
  exact ⟨⟨AdjoinRoot.root F, -AdjoinRoot.mk F F.divX,
    hinv, by rw [mul_comm]; exact hinv⟩, rfl⟩

theorem M5.Period.period_law : ∀ (F : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → 0 < M5.signaturePeriod F ∧ ∀ N : ℕ, F ∣ M5.cyclicModulus N ↔ M5.signaturePeriod F ∣ N := by
  change ∀ (F : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → 0 < M5.signaturePeriod F ∧ ∀ N : ℕ, F ∣ M5.cyclicModulus N ↔ M5.signaturePeriod F ∣ N
  intro F hmonic hcoeff
  letI : Finite (AdjoinRoot F) := M5.Period.quotient_finite F hmonic
  change 0 < orderOf (AdjoinRoot.root F) ∧ ∀ N : ℕ, F ∣ M5.cyclicModulus N ↔ orderOf (AdjoinRoot.root F) ∣ N
  constructor
  · exact orderOf_pos_iff.mpr (M5.Period.root_is_unit F hcoeff).isOfFinOrder
  · intro N
    rw [M5.Period.cyclic_dvd_iff_root_pow, orderOf_dvd_iff_pow_eq_one]

theorem M5.Period.period_dvd_of_dvd : ∀ (F G : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → G.Monic → G.coeff 0 = 1 → F ∣ G → M5.signaturePeriod F ∣ M5.signaturePeriod G := by
  change ∀ (F G : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → G.Monic → G.coeff 0 = 1 → F ∣ G → M5.signaturePeriod F ∣ M5.signaturePeriod G
  intro F G hFm hFc hGm hGc hFG
  apply ((M5.Period.period_law F hFm hFc).2 (M5.signaturePeriod G)).mp
  apply dvd_trans hFG
  exact ((M5.Period.period_law G hGm hGc).2 (M5.signaturePeriod G)).mpr (dvd_refl _)

theorem M5.Period.period_one : M5.signaturePeriod (1 : M5.BinaryPolynomial) = 1 := by
  change M5.signaturePeriod (1 : M5.BinaryPolynomial) = 1
  apply Nat.dvd_one.mp
  exact ((M5.Period.period_law (1 : M5.BinaryPolynomial)
    Polynomial.monic_one (by simp)).2 1).mp (one_dvd _)

theorem M5.Period.quotient_cardinality : ∀ F : M5.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree
  intro F hF
  classical
  calc
    Nat.card (AdjoinRoot F) = Nat.card (Fin F.natDegree → ZMod 2) :=
      Nat.card_congr ((AdjoinRoot.powerBasisAux' hF).equivFun.toEquiv)
    _ = 2 ^ F.natDegree := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem M5.Period.period_cardinality_bound : ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.signaturePeriod F ≤ 2 ^ F.natDegree := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.signaturePeriod F ≤ 2 ^ F.natDegree
  intro F hF h0
  letI : Finite (AdjoinRoot F) := M5.Period.quotient_finite F hF
  unfold M5.signaturePeriod
  calc
    orderOf (AdjoinRoot.root F) ≤ Nat.card (AdjoinRoot F) := orderOf_le_card
    _ = 2 ^ F.natDegree := M5.Period.quotient_cardinality F hF

theorem M5.CRT.interval_representative : ∀ R r w : ℕ, 0 < R → ∃ k : ℕ, w ≤ k ∧ k < w + R ∧ Nat.ModEq R k r := by
  change ∀ R r w : ℕ, 0 < R → ∃ k : ℕ, w ≤ k ∧ k < w + R ∧ Nat.ModEq R k r
  intro R r w hR
  cases R with
  | zero => omega
  | succ n =>
    refine ⟨w + (r + n * w) % (n + 1), by omega, ?_, ?_⟩
    · exact Nat.add_lt_add_left (Nat.mod_lt _ (by omega)) w
    · change (w + (r + n * w) % (n + 1)) % (n + 1) = r % (n + 1)
      calc
        (w + (r + n * w) % (n + 1)) % (n + 1) =
            (w + (r + n * w)) % (n + 1) := by
              simp only [Nat.add_mod, Nat.mod_mod]
        _ = (r + (n + 1) * w) % (n + 1) := by
              congr 1 <;> ring
        _ = r % (n + 1) := by simp [Nat.add_mod]

theorem M5.CRT.prime_crt_representative : ∀ δ e : ℕ, 0 < δ → ∃ r : ℕ, r < M5.CRT.primeProduct δ ∧ ∀ p ∈ δ.primeFactors, Nat.ModEq p r (M5.CRT.repairResidue e p) := by
  change ∀ δ e : ℕ, 0 < δ → ∃ r : ℕ, r < M5.CRT.primeProduct δ ∧ ∀ p ∈ δ.primeFactors, Nat.ModEq p r (M5.CRT.repairResidue e p)
  intro δ e hδ
  have hn : ∀ p ∈ δ.primeFactors, (fun p : ℕ => p) p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hc : Set.Pairwise (↑δ.primeFactors : Set ℕ) (fun p q => Nat.Coprime p q) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).2 hpq
  refine ⟨(Nat.chineseRemainderOfFinset (M5.CRT.repairResidue e) (fun p : ℕ => p) δ.primeFactors hn hc).val, ?_, ?_⟩
  · simpa [M5.CRT.primeProduct] using Nat.chineseRemainderOfFinset_lt_prod (M5.CRT.repairResidue e) (fun p : ℕ => p) hn hc
  · exact (Nat.chineseRemainderOfFinset (M5.CRT.repairResidue e) (fun p : ℕ => p) δ.primeFactors hn hc).property

theorem M5.CRT.safe_prime_residue : ∀ p δ T e : ℕ, p.Prime → p ∣ δ → Nat.gcd (Nat.gcd T δ) e = 1 → ¬ p ∣ e + M5.CRT.repairResidue e p * T := by
  change ∀ p δ T e : ℕ, p.Prime → p ∣ δ → Nat.gcd (Nat.gcd T δ) e = 1 → ¬ p ∣ e + M5.CRT.repairResidue e p * T
  intro p δ T e hp hδ hg
  by_cases he : p ∣ e
  · intro h
    have hsum : p ∣ e + T := by
      simpa [M5.CRT.repairResidue, he] using h
    have hT : p ∣ T := (Nat.dvd_add_right he).mp hsum
    have hd : p ∣ Nat.gcd (Nat.gcd T δ) e :=
      Nat.dvd_gcd (Nat.dvd_gcd hT hδ) he
    rw [hg] at hd
    exact hp.not_dvd_one hd
  · simpa [M5.CRT.repairResidue, he] using he

theorem M5.CRT.residues_force_coprime : ∀ δ T e k : ℕ, 0 < δ → Nat.gcd (Nat.gcd T δ) e = 1 → (∀ p ∈ δ.primeFactors, Nat.ModEq p k (M5.CRT.repairResidue e p)) → Nat.gcd δ (e + k * T) = 1 := by
  change ∀ δ T e k : ℕ, 0 < δ → Nat.gcd (Nat.gcd T δ) e = 1 → (∀ p ∈ δ.primeFactors, Nat.ModEq p k (M5.CRT.repairResidue e p)) → Nat.gcd δ (e + k * T) = 1
  intro δ T e k hδ hg hk
  apply Nat.coprime_of_dvd
  intro p hp hpδ hpe
  have hmem : p ∈ δ.primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hp, hpδ, Nat.ne_of_gt hδ⟩
  have hmod := ((hk p hmem).mul_right T).add_left e
  exact M5.CRT.safe_prime_residue p δ T e hp hpδ hg
    ((hmod.dvd_iff (dvd_refl p)).mp hpe)

theorem M5.CRT.bounded_connectivity_repair : ∀ δ T e w : ℕ, 0 < δ → 0 < T → Nat.gcd (Nat.gcd T δ) e = 1 → ∃ k : ℕ, w ≤ k ∧ k < w + δ ∧ Nat.gcd δ (e + k * T) = 1 := by
  change ∀ δ T e w : ℕ, 0 < δ → 0 < T → Nat.gcd (Nat.gcd T δ) e = 1 → ∃ k : ℕ, w ≤ k ∧ k < w + δ ∧ Nat.gcd δ (e + k * T) = 1
  intro δ T e w hδ hT hg
  obtain ⟨r, hrlt, hr⟩ := M5.CRT.prime_crt_representative δ e hδ
  obtain ⟨k, hwk, hklt, hkr⟩ := M5.CRT.interval_representative δ r w hδ
  refine ⟨k, hwk, hklt, ?_⟩
  apply M5.CRT.residues_force_coprime δ T e k hδ hg
  intro p hp
  have hpδ : p ∣ δ := (Nat.mem_primeFactors.mp hp).2.1
  have hkp : Nat.ModEq p k r := by
    first
    | exact Nat.ModEq.of_dvd hpδ hkr
    | exact hkr.of_dvd hpδ
  exact hkp.trans (hr p hp)

theorem M5.Packing.packed_support_anchor : ∀ (w T : ℕ) (r : Fin w → Fin T) (hw : 0 < w), (r ⟨0, hw⟩).val = 0 → 0 ∈ M5.Packing.packedSupport r := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (hw : 0 < w), (r ⟨0, hw⟩).val = 0 → 0 ∈ M5.Packing.packedSupport r
  intro w T r hw h
  unfold M5.Packing.packedSupport
  apply Finset.mem_image.mpr
  refine ⟨⟨0, hw⟩, Finset.mem_univ _, ?_⟩
  simp [M5.Packing.packedValue, M5.Packing.occurrenceTag, M5.Packing.priorOccurrences, Fin.lt_def, h]

theorem M5.Packing.tag_lt_weight : ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.occurrenceTag r i < w := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.occurrenceTag r i < w
  intro w T r i
  classical
  unfold M5.Packing.occurrenceTag
  have hs : M5.Packing.priorOccurrences r i ⊂ (Finset.univ : Finset (Fin w)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro h
    have hi : i ∈ M5.Packing.priorOccurrences r i := by
      rw [h]
      exact Finset.mem_univ i
    simpa [M5.Packing.priorOccurrences] using hi
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hs

theorem M5.Packing.packed_support_range : ∀ (w T : ℕ) (r : Fin w → Fin T) (e : ℕ), e ∈ M5.Packing.packedSupport r → e < w * T := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (e : ℕ), e ∈ M5.Packing.packedSupport r → e < w * T
  intro w T r e he
  classical
  unfold M5.Packing.packedSupport at he
  rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
  change (r i).val + M5.Packing.occurrenceTag r i * T < w * T
  have hr := (r i).isLt
  have ht := M5.Packing.tag_lt_weight w T r i
  have hm := Nat.mul_le_mul_right T (Nat.succ_le_of_lt ht)
  nlinarith

theorem M5.Packing.packed_support_card : ∀ (w T : ℕ) (r : Fin w → Fin T), (M5.Packing.packedSupport r).card = w := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), (M5.Packing.packedSupport r).card = w
  intro w T r
  classical
  unfold M5.Packing.packedSupport
  rw [Finset.card_image_of_injective _ (M5.Packing.packed_value_injective w T r)]
  simp

theorem M5.Character.bit_add : ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c := by
  change ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c
  decide

theorem M5.Character.bit_orthogonality : ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0 := by
  change ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
  decide

theorem M5.Character.character_add : ∀ (D : ℕ) (lam z u : M5.Character.BinaryVector D), M5.Character.value lam (z + u) = M5.Character.value lam z * M5.Character.value lam u := by
  change ∀ (D : ℕ) (lam z u : M5.Character.BinaryVector D), M5.Character.value lam (z + u) = M5.Character.value lam z * M5.Character.value lam u
  intro D lam z u
  simp only [M5.Character.value, Pi.add_apply, M5.Character.bit_add, Finset.prod_mul_distrib]

theorem M5.Character.character_orthogonality : ∀ (D : ℕ) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z) = if z = 0 then (2 : ℤ) ^ D else 0 := by
  change ∀ (D : ℕ) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z) = if z = 0 then (2 : ℤ) ^ D else 0
  intro D z
  classical
  change (∑ lam : Fin D → ZMod 2, ∏ i : Fin D, M5.Character.bitSign (lam i) (z i)) = if z = 0 then (2 : ℤ) ^ D else 0
  rw [← Fintype.prod_sum (fun (i : Fin D) (a : ZMod 2) => M5.Character.bitSign a (z i))]
  simp_rw [M5.Character.bit_orthogonality]
  by_cases h : z = 0
  · subst z
    simp
  · rw [if_neg h]
    have hex : ∃ i : Fin D, z i ≠ 0 := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem M5.Character.finite_fibre_count : ∀ (D n : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ u : Fin n, M5.Character.value lam (f u)) = (2 : ℤ) ^ D * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ) := by
  change ∀ (D n : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ u : Fin n, M5.Character.value lam (f u)) = (2 : ℤ) ^ D * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ)
  intro D n f z
  classical
  have hbit : ∀ a b : ZMod 2, a + b = 0 ↔ b = a := by
    decide
  have hz (u : Fin n) : z + f u = 0 ↔ f u = z := by
    constructor
    · intro h
      funext i
      exact (hbit (z i) (f u i)).mp (congrFun h i)
    · intro h
      funext i
      exact (hbit (z i) (f u i)).mpr (congrFun h i)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← M5.Character.character_add, M5.Character.character_orthogonality, hz]
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem M5.SupportPolynomial.packed_sum_image : ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) → M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r) = ∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ M5.Packing.packedValue r i := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) → M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r) = ∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ M5.Packing.packedValue r i
  intro w T r hinj
  classical
  unfold M5.SupportPolynomial.ofSupport M5.Packing.packedSupport
  apply Finset.sum_image
  intro i hi j hj hij
  exact hinj hij

theorem M5.SupportPolynomial.quotient_monomial_period : ∀ T a j : ℕ, AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) = AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ a) := by
  change ∀ T a j : ℕ, AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) = AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ a)
  intro T a j
  let q := AdjoinRoot.mk (M5.cyclicModulus T)
  have htwo : (1 : M5.BinaryPolynomial) + 1 = 0 := by
    have h : (1 : ZMod 2) + 1 = 0 := by decide
    simpa only [map_add, Polynomial.C_1, map_zero] using congrArg (Polynomial.C : ZMod 2 → M5.BinaryPolynomial) h
  have htwoq : (1 : AdjoinRoot (M5.cyclicModulus T)) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg q htwo
  have hmod : q ((Polynomial.X : M5.BinaryPolynomial) ^ T + 1) = 0 := by
    change AdjoinRoot.mk (M5.cyclicModulus T) (M5.cyclicModulus T) = 0
    exact AdjoinRoot.mk_self
  have hsum : q Polynomial.X ^ T + 1 = 0 := by
    simpa only [map_add, map_pow, map_one] using hmod
  have hpow : q Polynomial.X ^ T = 1 := by
    apply add_right_cancel (b := (1 : AdjoinRoot (M5.cyclicModulus T)))
    exact hsum.trans htwoq.symm
  change q (Polynomial.X ^ (a + j * T)) = q (Polynomial.X ^ a)
  rw [map_pow, map_pow, pow_add, Nat.mul_comm j T, pow_mul, hpow, one_pow, mul_one]

theorem M5.SupportPolynomial.support_coeff_zero : ∀ S : Finset ℕ, (M5.SupportPolynomial.ofSupport S).coeff 0 = if 0 ∈ S then 1 else 0 := by
  classical
  intro S
  simp [M5.SupportPolynomial.ofSupport, Polynomial.coeff_X_pow]

theorem M5.SupportPolynomial.support_degree_bound : ∀ (S : Finset ℕ) (K : ℕ), 0 < K → (∀ e ∈ S, e < K) → (M5.SupportPolynomial.ofSupport S).natDegree < K := by
  change ∀ (S : Finset ℕ) (K : ℕ), 0 < K → (∀ e ∈ S, e < K) → (M5.SupportPolynomial.ofSupport S).natDegree < K
  intro S K hK
  induction S using Finset.induction_on with
  | empty =>
      intro hS
      simpa [M5.SupportPolynomial.ofSupport] using hK
  | @insert a S ha ih =>
      intro hS
      rw [M5.SupportPolynomial.ofSupport, Finset.sum_insert ha]
      apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      apply max_lt_iff.mpr
      constructor
      · simpa only [Polynomial.natDegree_X_pow] using hS a (Finset.mem_insert_self a S)
      · simpa only [M5.SupportPolynomial.ofSupport] using
          ih (fun e he => hS e (Finset.mem_insert_of_mem he))

theorem M5.SupportPolynomial.anchored_support_nonzero : ∀ S : Finset ℕ, 0 ∈ S → M5.SupportPolynomial.ofSupport S ≠ 0 := by
  change ∀ S : Finset ℕ, 0 ∈ S → M5.SupportPolynomial.ofSupport S ≠ 0
  intro S hS hzero
  have hcoeff := M5.SupportPolynomial.support_coeff_zero S
  simpa [hzero, hS] using hcoeff

theorem M5.SupportPolynomial.packed_polynomial_residue : ∀ (w T : ℕ) (r : Fin w → Fin T), AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r)) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofResidueTuple r) := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r)) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofResidueTuple r)
  intro w T r
  classical
  rw [M5.SupportPolynomial.packed_sum_image w T r (by apply M5.Packing.packed_value_injective)]
  unfold M5.SupportPolynomial.ofResidueTuple
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold M5.Packing.packedValue
  apply M5.SupportPolynomial.quotient_monomial_period

theorem M5.Connectivity.divisor_moebius : ∀ n : ℕ, (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0 := by
  change ∀ n : ℕ, (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0
  intro n
  rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius, ArithmeticFunction.one_apply]

theorem M5.Connectivity.support_gcd_dvd : ∀ (N d : ℕ) (A B : Finset ℕ), d ∣ M5.Connectivity.supportGcd N A B ↔ d ∣ N ∧ (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) := by
  intro N d A B
  simp [M5.Connectivity.supportGcd, Nat.dvd_gcd_iff, Finset.dvd_gcd_iff, and_assoc]

theorem M5.Connectivity.support_divisor_filter : ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → N.divisors.filter (fun d => (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b)) = (M5.Connectivity.supportGcd N A B).divisors := by
  intro N A B hN
  have hdiv : M5.Connectivity.supportGcd N A B ∣ N :=
    ((M5.Connectivity.support_gcd_dvd N
      (M5.Connectivity.supportGcd N A B) A B).mp dvd_rfl).1
  have hg : M5.Connectivity.supportGcd N A B ≠ 0 := by
    intro hz
    rw [hz] at hdiv
    exact (Nat.ne_of_gt hN) (Nat.zero_dvd.mp hdiv)
  ext d
  simp [Finset.mem_filter, Nat.mem_divisors, Nat.ne_of_gt hN, hg,
    M5.Connectivity.support_gcd_dvd, and_assoc]

theorem M5.Connectivity.connected_indicator : ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → (∑ d ∈ N.divisors, if (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) then ArithmeticFunction.moebius d else 0) = if M5.Connectivity.supportGcd N A B = 1 then (1 : ℤ) else 0 := by
  classical
  change ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → (∑ d ∈ N.divisors, if (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) then ArithmeticFunction.moebius d else 0) = if M5.Connectivity.supportGcd N A B = 1 then (1 : ℤ) else 0
  intro N A B hN
  rw [← Finset.sum_filter, M5.Connectivity.support_divisor_filter N A B hN,
    M5.Connectivity.divisor_moebius]

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
