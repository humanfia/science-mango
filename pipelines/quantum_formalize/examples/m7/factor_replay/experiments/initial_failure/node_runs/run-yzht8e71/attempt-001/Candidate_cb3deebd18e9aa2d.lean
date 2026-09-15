import FrozenTarget_cb3deebd18e9aa2d
theorem M7.FactorReplay.pool_complete : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (p : M7.FactorReplay.BP), p ∈ M7.FactorReplay.pool n ↔ p.natDegree ≤ n
  intro n p
  classical
  unfold M7.FactorReplay.pool
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, _, rfl⟩
    have h : (Polynomial.ofFn v).natDegree < n + 1 := by
      apply Polynomial.ofFn_natDegree_lt
      omega
    omega
  · intro hp
    refine ⟨Polynomial.toFn (n + 1) p, Finset.mem_univ _, ?_⟩
    apply Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
    omega
