import FrozenTarget_834ebd08efa2346b
theorem M5.Character.finite_fibre_count : QuantumHarnessFrozenTarget := by
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
