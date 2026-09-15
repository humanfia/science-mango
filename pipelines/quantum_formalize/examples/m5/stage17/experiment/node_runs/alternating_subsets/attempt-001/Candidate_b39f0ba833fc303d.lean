import FrozenTarget_b39f0ba833fc303d
theorem M5.FiniteExclusion.alternating_subsets : QuantumHarnessFrozenTarget := by
  classical
  change ∀ S : Finset M5.BinaryPolynomial, (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card) = if S = ∅ then 1 else 0
  intro S
  first
    | exact Finset.sum_powerset_neg_one_pow_card
    | exact Nat.sum_powerset_neg_one_pow_card
