import M5Translation

theorem M5.Translation.anchored_difference_gcd : ∀ (N : ℕ) [NeZero N] (S U : Finset (ZMod N)), 0 ∈ S → 0 ∈ U → M5.Translation.differenceGcd S U = M5.Connectivity.supportGcd N (M5.Translation.natSupport S) (M5.Translation.natSupport U) := by
  change ∀ (N : ℕ) [NeZero N] (S U : Finset (ZMod N)), _
  intro N inst S U hS hU
  classical
  have hsub (d : ℕ) (hd : d ∣ N) (x y : ZMod N)
      (hx : d ∣ x.val) (hy : d ∣ y.val) : d ∣ (x - y).val := by
    by_cases hy0 : y = 0
    · simpa [hy0] using hx
    · letI : NeZero y := ⟨hy0⟩
      rw [sub_eq_add_neg, ZMod.val_add, ZMod.val_neg_of_ne_zero]
      exact (Nat.dvd_mod_iff hd).2 (dvd_add hx (Nat.dvd_sub hd hy))
  have hbase (d : ℕ) (A : Finset (ZMod N)) :
      (∀ a ∈ M5.Translation.natSupport A, d ∣ a) ↔
        (∀ x ∈ A, d ∣ x.val) := by
    constructor
    · intro h x hx
      exact h x.val (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · intro h a ha
      rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
      exact h x hx
  have hdiff (d : ℕ) (A : Finset (ZMod N)) :
      (∀ a ∈ M5.Translation.natSupport (M5.Translation.differences A), d ∣ a) ↔
        (∀ x ∈ A, ∀ y ∈ A, d ∣ (x - y).val) := by
    rw [hbase]
    constructor
    · intro h x hx y hy
      apply h (x - y)
      simp only [M5.Translation.differences, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨x, hx, y, hy, rfl⟩
    · intro h z hz
      have hz' : ∃ x ∈ A, ∃ y ∈ A, x - y = z := by
        simpa [M5.Translation.differences] using hz
      rcases hz' with ⟨x, hx, y, hy, rfl⟩
      exact h x hx y hy
  have hanch (d : ℕ) (hd : d ∣ N) (A : Finset (ZMod N)) (hA : 0 ∈ A) :
      (∀ a ∈ M5.Translation.natSupport (M5.Translation.differences A), d ∣ a) ↔
        (∀ a ∈ M5.Translation.natSupport A, d ∣ a) := by
    rw [hdiff, hbase]
    constructor
    · intro h x hx
      simpa using h x hx 0 hA
    · intro h x hx y hy
      exact hsub d hd x y (h x hx) (h y hy)
  have hequiv (d : ℕ) :
      d ∣ M5.Translation.differenceGcd S U ↔
        d ∣ M5.Connectivity.supportGcd N (M5.Translation.natSupport S) (M5.Translation.natSupport U) := by
    unfold M5.Translation.differenceGcd
    rw [M5.Connectivity.support_gcd_dvd, M5.Connectivity.support_gcd_dvd]
    constructor
    · rintro ⟨hd, hs, hu⟩
      exact ⟨hd, (hanch d hd S hS).1 hs, (hanch d hd U hU).1 hu⟩
    · rintro ⟨hd, hs, hu⟩
      exact ⟨hd, (hanch d hd S hS).2 hs, (hanch d hd U hU).2 hu⟩
  apply Nat.dvd_antisymm
  · exact (hequiv _).1 (dvd_refl _)
  · exact (hequiv _).2 (dvd_refl _)

theorem M5.Translation.difference_translation : ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (c : ZMod N), M5.Translation.differences (M5.Translation.shift S c) = M5.Translation.differences S := by
  intro N inst S c
  classical
  have hs (x : ZMod N) : x ∈ M5.Translation.shift S c ↔ x - c ∈ S := by
    simp [M5.Translation.shift, sub_eq_add_neg]
  ext z
  simp only [M5.Translation.differences, Finset.mem_biUnion, Finset.mem_image, hs]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨x - c, hx, y - c, hy, ?_⟩
    calc
      (x - c) - (y - c) = x - y := by abel
      _ = z := hxy
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨x + c, ?_, y + c, ?_, ?_⟩
    · simpa using hx
    · simpa using hy
    · calc
        (x + c) - (y + c) = x - y := by abel
        _ = z := hxy

theorem M5.Translation.shift_card_anchor : ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (c : ZMod N), c ∈ S → (M5.Translation.shift S (-c)).card = S.card ∧ 0 ∈ M5.Translation.shift S (-c) := by
  intro N inst S c hc
  classical
  unfold M5.Translation.shift
  constructor
  · apply Finset.card_image_iff.mpr
    intro a ha b hb h
    dsimp at h
    first
    | exact add_right_cancel h
    | exact add_left_cancel h
  · apply Finset.mem_image.mpr
    exact ⟨c, hc, by simp⟩

theorem M5.Translation.shift_quotient_polynomial : ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (c : ZMod N), AdjoinRoot.mk (M5.cyclicModulus N) (M5.Translation.supportPolynomial (M5.Translation.shift S c)) = AdjoinRoot.mk (M5.cyclicModulus N) ((Polynomial.X : M5.BinaryPolynomial) ^ c.val) * AdjoinRoot.mk (M5.cyclicModulus N) (M5.Translation.supportPolynomial S) := by
  classical
  intro N inst S c
  have hsupport (A : Finset (ZMod N)) :
      M5.Translation.supportPolynomial A =
        ∑ x ∈ A, (Polynomial.X : M5.BinaryPolynomial) ^ x.val := by
    change (∑ e ∈ A.image ZMod.val, (Polynomial.X : M5.BinaryPolynomial) ^ e) = _
    apply Finset.sum_image
    intro x hx y hy h
    exact ZMod.val_injective N h
  rw [hsupport, hsupport]
  unfold M5.Translation.shift
  rw [Finset.sum_image]
  · simp only [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have he : (c.val + x.val) % N + (c.val + x.val) / N * N =
        c.val + x.val := by
      simpa [Nat.mul_comm] using Nat.mod_add_div (c.val + x.val) N
    have hp := M5.SupportPolynomial.quotient_monomial_period N
      ((c.val + x.val) % N) ((c.val + x.val) / N)
    rw [he] at hp
    rw [ZMod.val_add, Nat.add_comm x.val c.val, ← hp, pow_add, map_mul]
  · intro x hx y hy h
    exact add_right_cancel h

theorem M5.Translation.signature_translation : ∀ (N : ℕ) [NeZero N] (S U : Finset (ZMod N)) (c d : ZMod N), M5.completeSignature (M5.Translation.supportPolynomial (M5.Translation.shift S c)) (M5.Translation.supportPolynomial (M5.Translation.shift U d)) N = M5.completeSignature (M5.Translation.supportPolynomial S) (M5.Translation.supportPolynomial U) N := by
  classical
  intro N inst S U c d
  have hforward (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N)
      (h : D ∣ M5.Translation.supportPolynomial A) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) := by
    apply (M5.SignatureCongruence.divisibility_of_quotient_eq D
      (M5.Translation.supportPolynomial (M5.Translation.shift A e))
      ((Polynomial.X : M5.BinaryPolynomial) ^ e.val * M5.Translation.supportPolynomial A)
      N hD (by
        simpa only [map_mul] using M5.Translation.shift_quotient_polynomial N A e)).2
    exact dvd_mul_of_dvd_right h _
  have hcancel (A : Finset (ZMod N)) (e : ZMod N) :
      M5.Translation.shift (M5.Translation.shift A e) (-e) = A := by
    unfold M5.Translation.shift
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, he⟩
      have hzx : z = x := by simpa using he
      simpa [hzx] using hz
    · intro hx
      exact ⟨x + e, ⟨x, hx, rfl⟩, by simp⟩
  have hshift (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) ↔
        D ∣ M5.Translation.supportPolynomial A := by
    constructor
    · intro h
      have hh := hforward D hD (M5.Translation.shift A e) (-e) h
      simpa only [hcancel] using hh
    · exact hforward D hD A e
  have hg (D a b : M5.BinaryPolynomial) :
      D ∣ EuclideanDomain.gcd a b ↔ D ∣ a ∧ D ∣ b := by
    constructor
    · intro h
      exact ⟨dvd_trans h (EuclideanDomain.gcd_dvd_left a b),
        dvd_trans h (EuclideanDomain.gcd_dvd_right a b)⟩
    · rintro ⟨ha, hb⟩
      exact EuclideanDomain.dvd_gcd ha hb
  have hs (D a b : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature a b N ↔
        D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus N := by
    simp only [M5.completeSignature, hg, and_assoc]
  have he (D : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature
        (M5.Translation.supportPolynomial (M5.Translation.shift S c))
        (M5.Translation.supportPolynomial (M5.Translation.shift U d)) N ↔
      D ∣ M5.completeSignature
        (M5.Translation.supportPolynomial S)
        (M5.Translation.supportPolynomial U) N := by
    rw [hs, hs]
    constructor
    · rintro ⟨hS, hU, hN⟩
      exact ⟨(hshift D hN S c).1 hS, (hshift D hN U d).1 hU, hN⟩
    · rintro ⟨hS, hU, hN⟩
      exact ⟨(hshift D hN S c).2 hS, (hshift D hN U d).2 hU, hN⟩
  apply M5.Signature.binary_dvd_antisymm
  · exact (he _).1 dvd_rfl
  · exact (he _).2 dvd_rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (S U : Finset (ZMod N)), S.Nonempty → U.Nonempty → ∃ A B : Finset ℕ, A.card = S.card ∧ B.card = U.card ∧ 0 ∈ A ∧ 0 ∈ B ∧ (∀ a ∈ A, a < N) ∧ (∀ b ∈ B, b < N) ∧ M5.Connectivity.supportGcd N A B = M5.Translation.differenceGcd S U ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = M5.completeSignature (M5.Translation.supportPolynomial S) (M5.Translation.supportPolynomial U) N
