import FrozenTarget_2c1a3a87e9f60f81
theorem M8.Solver.originalF_signature : QuantumHarnessFrozenTarget := by
  intro N inst c
  classical
  have hs : ∀ s : Finset (ZMod N), (M7.Supports.polynomial s).natDegree ≤ N := by
    intro s
    by_cases hz : M7.Supports.polynomial s = 0
    · simp [hz]
    · have hm := Polynomial.natDegree_mem_support_of_nonzero hz
      rw [M7.Supports.support] at hm
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
      exact he ▸ (Nat.le_of_lt (ZMod.val_lt i))
  have ha := hs c.1
  have hb := hs c.2
  have hm : (M6.Cyclic.modulus N).natDegree ≤ N := by
    unfold M6.Cyclic.modulus
    exact le_trans Polynomial.natDegree_sub_le (by simp)
  unfold M8.Solver.originalF M8.PhysicalBridge.signature M7.RecipeSignature.signature
  solve_by_elim (maxDepth := 8) only [M6.Euclid.preprocess_correct_cost, And.left, And.right, ha, hb, hm]
