import M5AnchoredTupleCount

theorem M5.AnchoredTupleCount.anchored_tuple_divisibility : ∀ (P : M5.BinaryPolynomial) (T d k : ℕ) (t : Fin k → Fin (T / d)), (P ∣ 1 + M5.ArithmeticTuple.tuplePolynomial T d k t ↔ AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = 1) := by
  intro P T d k t
  have hb : (1 : ZMod 2) + 1 = 0 := by decide
  have hp : (1 : M5.BinaryPolynomial) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using
      congrArg (Polynomial.C : ZMod 2 → M5.BinaryPolynomial) hb
  have htwo : (1 : AdjoinRoot P) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (AdjoinRoot.mk P) hp
  rw [← AdjoinRoot.mk_eq_zero, map_add, map_one]
  constructor
  · intro h
    exact add_left_cancel (h.trans htwo.symm)
  · intro h
    rw [h]
    exact htwo

theorem M5.AnchoredTupleCount.multiples_equivalence : ∀ T d : ℕ, 0 < T → d ∣ T → ∃ e : Fin (T / d) ≃ {r : Fin T // d ∣ r.val}, ∀ j : Fin (T / d), (e j).val.val = d * j.val := by
  change ∀ T d : ℕ, 0 < T → d ∣ T → ∃ e : Fin (T / d) ≃ {r : Fin T // d ∣ r.val}, ∀ j : Fin (T / d), (e j).val.val = d * j.val
  intro T d hT hdT
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    subst d
    have hzT : T = 0 := by simpa using hdT
    omega
  have hrecover : ∀ n : ℕ, d ∣ n → d * (n / d) = n := by
    intro n hn
    simpa [Nat.mul_comm] using Nat.div_mul_cancel hn
  have htotal : d * (T / d) = T := hrecover T hdT
  have hforward : ∀ j : Fin (T / d), d * j.val < T := by
    intro j
    have h := Nat.mul_lt_mul_of_pos_left j.isLt hd
    omega
  have hback : ∀ r : {r : Fin T // d ∣ r.val}, r.val.val / d < T / d := by
    intro r
    by_contra h
    have hle : T / d ≤ r.val.val / d := by omega
    have hm := Nat.mul_le_mul_left d hle
    have hr := hrecover r.val.val r.property
    have hb := r.val.isLt
    omega
  refine ⟨{
    toFun := fun j => ⟨⟨d * j.val, hforward j⟩, ⟨j.val, rfl⟩⟩
    invFun := fun r => ⟨r.val.val / d, hback r⟩
    left_inv := ?_
    right_inv := ?_
  }, ?_⟩
  · intro j
    apply Fin.ext
    change d * j.val / d = j.val
    exact Nat.mul_div_cancel_left j.val hd
  · intro r
    apply Subtype.ext
    apply Fin.ext
    change d * (r.val.val / d) = r.val.val
    exact hrecover r.val.val r.property
  · intro j
    rfl

theorem M5.AnchoredTupleCount.anchored_R_count : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ), M5.ArithmeticTuple.R P hP T d k 1 = (M5.AnchoredTupleCount.count P T d k : ℤ) := by
  intro P hP T d k
  classical
  rw [M5.ArithmeticTuple.R_exact]
  simp only [M5.AnchoredTupleCount.count,
    M5.AnchoredTupleCount.anchored_tuple_divisibility]

theorem M5.AnchoredTupleCount.restricted_R_count : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ), 0 < T → d ∣ T → M5.ArithmeticTuple.R P hP T d k 1 = (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ) := by
  change ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ), 0 < T → d ∣ T → M5.ArithmeticTuple.R P hP T d k 1 = (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ)
  intro P hP T d k hT hdT
  classical
  rw [M5.AnchoredTupleCount.anchored_R_count]
  apply congrArg (fun n : ℕ => (n : ℤ))
  obtain ⟨e, he⟩ := M5.AnchoredTupleCount.multiples_equivalence T d hT hdT
  let f : (Fin k → Fin (T / d)) → (Fin k → Fin T) := fun t i => (e (t i)).val
  have hp : ∀ t, (∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (f t i).val) = M5.ArithmeticTuple.tuplePolynomial T d k t := by
    intro t
    unfold M5.ArithmeticTuple.tuplePolynomial
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact he (t i)
  unfold M5.AnchoredTupleCount.count M5.AnchoredTupleCount.restrictedCount
  apply Finset.card_bij (fun t _ => f t)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      M5.SupportPolynomial.ofResidueTuple] at ht ⊢
    have hdiv : ∀ i : Fin k, d ∣ (f t i).val := fun i => (e (t i)).property
    have hg : P ∣ 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (f t i).val := by
      rw [hp]
      exact ht
    aesop
  · intro t ht u hu h
    funext i
    apply e.injective
    apply Subtype.ext
    exact congrFun h i
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      M5.SupportPolynomial.ofResidueTuple] at hr
    have hdiv : ∀ i : Fin k, d ∣ (r i).val := by aesop
    have hg : P ∣ 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (r i).val := by aesop
    let t : Fin k → Fin (T / d) := fun i => e.symm ⟨r i, hdiv i⟩
    have hf : f t = r := by
      funext i
      change (e (e.symm ⟨r i, hdiv i⟩)).val = r i
      exact congrArg Subtype.val (e.apply_symm_apply ⟨r i, hdiv i⟩)
    refine ⟨t, ?_, hf⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change P ∣ 1 + M5.ArithmeticTuple.tuplePolynomial T d k t
    rw [← hp t, hf]
    exact hg
#print axioms M5.AnchoredTupleCount.anchored_tuple_divisibility
#print axioms M5.AnchoredTupleCount.anchored_R_count
#print axioms M5.AnchoredTupleCount.multiples_equivalence
#print axioms M5.AnchoredTupleCount.restricted_R_count
