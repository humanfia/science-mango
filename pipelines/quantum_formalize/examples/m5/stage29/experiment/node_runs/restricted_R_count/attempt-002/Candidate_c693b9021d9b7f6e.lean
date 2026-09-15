import FrozenTarget_c693b9021d9b7f6e
theorem M5.AnchoredTupleCount.restricted_R_count : QuantumHarnessFrozenTarget := by
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
