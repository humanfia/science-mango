import FrozenTarget_a7e4ac77932b681f
theorem M5.TupleCompletion.restricted_completion_R : QuantumHarnessFrozenTarget := by
  intro P hP Z T d k hT hd
  classical
  rw [M5.TupleCompletion.completion_R_count]
  apply congrArg (fun n : ℕ => (n : ℤ))
  unfold M5.TupleCompletion.count M5.TupleCompletion.restrictedCount
  obtain ⟨e, he⟩ := M5.AnchoredTupleCount.multiples_equivalence T d hT hd
  let f : (Fin k → Fin (T / d)) → (Fin k → Fin T) := fun t i => (e (t i)).val
  have hfdiv (t : Fin k → Fin (T / d)) : ∀ i, d ∣ (f t i).val :=
    fun i => (e (t i)).property
  have hfpoly (t : Fin k → Fin (T / d)) :
      M5.SupportPolynomial.ofResidueTuple (f t) = M5.ArithmeticTuple.tuplePolynomial T d k t := by
    simp [M5.SupportPolynomial.ofResidueTuple, M5.ArithmeticTuple.tuplePolynomial, f, he]
  refine Finset.card_bij (fun t _ => f t) ?_ ?_ ?_
  · intro t ht
    simpa [Finset.mem_filter, hfdiv t, hfpoly t] using ht
  · intro t ht u hu h
    funext i
    apply e.injective
    apply Subtype.ext
    exact congrFun h i
  · intro r hr
    have hr' := hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
    have hrd : ∀ i, d ∣ (r i).val := by aesop
    have hrP : P ∣ Z + M5.SupportPolynomial.ofResidueTuple r := by aesop
    let t : Fin k → Fin (T / d) := fun i => e.symm ⟨r i, hrd i⟩
    have hft : f t = r := by
      funext i
      exact congrArg Subtype.val (e.apply_symm_apply ⟨r i, hrd i⟩)
    refine ⟨t, ?_, hft⟩
    have hp : M5.ArithmeticTuple.tuplePolynomial T d k t = M5.SupportPolynomial.ofResidueTuple r := by
      rw [← hfpoly t, hft]
    simpa [Finset.mem_filter, hp] using hrP
