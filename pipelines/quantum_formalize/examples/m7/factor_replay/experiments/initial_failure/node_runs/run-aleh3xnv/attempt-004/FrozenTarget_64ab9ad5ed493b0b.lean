import M7FactorReplay

theorem M7.FactorReplay.pool_complete : ∀ (n : ℕ) (p : M7.FactorReplay.BP), p ∈ M7.FactorReplay.pool n ↔ p.natDegree ≤ n := by
  change ∀ (n : ℕ) (p : M7.FactorReplay.BP), p ∈ M7.FactorReplay.pool n ↔ p.natDegree ≤ n
  intro n p
  classical
  unfold M7.FactorReplay.pool
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, _, rfl⟩
    have h := Polynomial.ofFn_natDegree_lt (show 1 ≤ n + 1 by omega) v
    omega
  · intro hp
    refine ⟨Polynomial.toFn (n + 1) p, Finset.mem_univ _, ?_⟩
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ p : M7.FactorReplay.BP, M7.FactorReplay.irreducibleCheck p = true ↔ p.Monic ∧ Irreducible p
