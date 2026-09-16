import FrozenTarget_2811a293c57ea9e3
theorem M8.Solver.originalF_signature : QuantumHarnessFrozenTarget := by
  intro N inst c
  classical
  have hb (s : Finset (ZMod N)) : (M7.Supports.polynomial s).natDegree ≤ N := by
    by_cases hz : M7.Supports.polynomial s = 0
    · simp [hz]
    · have hm := Polynomial.natDegree_mem_support_of_nonzero hz
      rw [M7.Supports.support] at hm
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
      rw [← he]
      exact Nat.le_of_lt (ZMod.val_lt i)
  have h₁ := hb c.1
  have h₂ := hb c.2
  have h₃ : (M6.Cyclic.modulus N).natDegree ≤ N := by
    unfold M6.Cyclic.modulus
    calc
      _ ≤ max (Polynomial.X ^ N : M6.Cyclic.BinaryPolynomial).natDegree (1 : M6.Cyclic.BinaryPolynomial).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ N := by simp
  dsimp [M8.Solver.originalF, M8.PhysicalBridge.signature, M7.RecipeSignature.signature]
  aesop (add safe forward M6.Euclid.preprocess_correct_cost)
