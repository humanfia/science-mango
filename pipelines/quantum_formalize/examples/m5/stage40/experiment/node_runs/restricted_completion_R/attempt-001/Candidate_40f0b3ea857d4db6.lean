import FrozenTarget_40f0b3ea857d4db6
theorem M5.TupleCompletion.restricted_completion_R : QuantumHarnessFrozenTarget := by
  intro P hP Z T d k hT hdT
  classical
  rw [M5.TupleCompletion.completion_R_count]
  apply congrArg (fun n : ℕ => (n : ℤ))
  obtain ⟨e, he⟩ := M5.AnchoredTupleCount.multiples_equivalence T d hT hdT
  let f : (Fin k → Fin (T / d)) → (Fin k → Fin T) :=
    fun t i => (e (t i)).val
  unfold M5.TupleCompletion.count M5.TupleCompletion.restrictedCount
  apply Finset.card_bij (fun t _ => f t)
  · intro t ht
    simpa [Finset.mem_filter, f, he, M5.ArithmeticTuple.tuplePolynomial,
      M5.SupportPolynomial.ofResidueTuple] using ht
  · intro t ht u hu h
    funext i
    apply e.injective
    apply Subtype.ext
    exact congrFun h i
  · intro r hr
    have hdr : ∀ i, d ∣ (r i).val := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      first | exact hr.1 | exact hr.2
    let t : Fin k → Fin (T / d) := fun i => e.symm ⟨r i, hdr i⟩
    have htr : f t = r := by
      funext i
      exact congrArg Subtype.val (e.apply_symm_apply ⟨r i, hdr i⟩)
    refine ⟨t, ?_, htr⟩
    rw [← htr] at hr
    simpa [Finset.mem_filter, f, he, M5.ArithmeticTuple.tuplePolynomial,
      M5.SupportPolynomial.ofResidueTuple] using hr
