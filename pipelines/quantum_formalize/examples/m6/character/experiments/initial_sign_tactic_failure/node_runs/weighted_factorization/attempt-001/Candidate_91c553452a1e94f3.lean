import FrozenTarget_91c553452a1e94f3
theorem M6.Character.weighted_factorization : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (w : Fin m → ZMod 2 → Polynomial ℤ) (q : M6.Character.Vector m), M6.Character.localTransform w q = ∑ z : M6.Character.Vector m, Polynomial.C (M6.Character.character q z) * ∏ i, w i (z i)
  intro m w q
  classical
  unfold M6.Character.localTransform
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [M6.Character.character_product, map_prod, Finset.prod_mul_distrib, mul_comm]
