import FrozenTarget_58722d3ec7a4fa4c
theorem M8.Diagonal.delta_weight : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ j : ZMod N, M6.Physical.weight N (M6.Physical.delta N j) = 1
  intro N inst j
  classical
  have hs : (Finset.univ.filter fun i : ZMod N => M6.Physical.delta N j i ≠ 0) = {j} := by
    ext i
    by_cases h : i = j <;> simp [M6.Physical.delta, h, eq_comm]
  change (Finset.univ.filter fun i : ZMod N => M6.Physical.delta N j i ≠ 0).card = 1
  rw [hs]
  exact Finset.card_singleton j
