import FrozenTarget_3534a6e52d4a1647
theorem M5.AnchoredTupleCount.restricted_R_count : QuantumHarnessFrozenTarget := by
  intro P hP T d k hT hdT
  classical
  rw [M5.AnchoredTupleCount.anchored_R_count]
  apply congrArg (fun n : ℕ => (n : ℤ))
  obtain ⟨e, he⟩ := M5.AnchoredTupleCount.multiples_equivalence T d hT hdT
  have hpoly (t : Fin k → Fin (T / d)) :
      (∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (e (t i)).val.val) =
        M5.ArithmeticTuple.tuplePolynomial T d k t := by
    unfold M5.ArithmeticTuple.tuplePolynomial
    simp only [he]
  unfold M5.AnchoredTupleCount.count M5.AnchoredTupleCount.restrictedCount
  refine Finset.card_bij (fun t _ => fun i => (e (t i)).val) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    have hd : ∀ i : Fin k, d ∣ (e (t i)).val.val := fun i => (e (t i)).property
    have hp : P ∣ 1 + ∑ i : Fin k,
        (Polynomial.X : M5.BinaryPolynomial) ^ (e (t i)).val.val := by
      rw [hpoly]
      exact ht
    simp only [M5.SupportPolynomial.ofResidueTuple]
    first | exact ⟨hd, hp⟩ | exact ⟨hp, hd⟩
  · intro t ht u hu htu
    funext i
    apply e.injective
    apply Subtype.ext
    exact congrFun htu i
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      M5.SupportPolynomial.ofResidueTuple] at hr
    have hd : ∀ i : Fin k, d ∣ (r i).val := by tauto
    have hp : P ∣ 1 + ∑ i : Fin k,
        (Polynomial.X : M5.BinaryPolynomial) ^ (r i).val := by tauto
    let t : Fin k → Fin (T / d) := fun i => e.symm ⟨r i, hd i⟩
    have hcoord : ∀ i : Fin k, (e (t i)).val = r i := by
      intro i
      exact congrArg Subtype.val (e.apply_symm_apply ⟨r i, hd i⟩)
    refine ⟨t, ?_, funext hcoord⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [← hpoly t, hcoord] using hp
