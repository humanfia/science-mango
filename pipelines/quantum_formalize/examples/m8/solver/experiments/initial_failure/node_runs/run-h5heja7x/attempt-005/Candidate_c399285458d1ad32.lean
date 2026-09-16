import FrozenTarget_c399285458d1ad32
theorem M8.Solver.originalF_signature : QuantumHarnessFrozenTarget := by
  intro N inst c
  classical
  have hdeg (s : Finset (ZMod N)) : (M7.Supports.polynomial s).natDegree ≤ N := by
    by_cases hz : M7.Supports.polynomial s = 0
    · simp [hz]
    · have hm := Polynomial.natDegree_mem_support_of_nonzero hz
      rw [M7.Supports.support] at hm
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
      rw [← he]
      exact Nat.le_of_lt (ZMod.val_lt i)
  have ha := hdeg c.1
  have hb := hdeg c.2
  have hm : (M6.Cyclic.modulus N).natDegree ≤ N := by
    unfold M6.Cyclic.modulus
    first
    | simpa using (Polynomial.natDegree_sub_le (Polynomial.X ^ N : M6.Cyclic.BinaryPolynomial) 1)
    | simpa using (Polynomial.natDegree_add_le (Polynomial.X ^ N : M6.Cyclic.BinaryPolynomial) 1)
  simp only [M8.Solver.originalF, M8.PhysicalBridge.signature, M7.RecipeSignature.signature]
  aesop (add safe forward M6.Euclid.preprocess_correct_cost)
