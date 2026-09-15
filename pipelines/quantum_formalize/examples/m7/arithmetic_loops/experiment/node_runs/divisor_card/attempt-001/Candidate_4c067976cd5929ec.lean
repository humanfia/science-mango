import FrozenTarget_4c067976cd5929ec
theorem M7.ArithmeticLoops.divisor_card : QuantumHarnessFrozenTarget := by
  intro N hN A B
  change (M5.Connectivity.supportGcd N A B).divisors.card ≤ N.divisors.card
  apply Finset.card_le_card
  intro d hd
  apply Nat.mem_divisors.mpr
  refine ⟨dvd_trans (Nat.mem_divisors.mp hd).1 ?_, Nat.ne_of_gt hN⟩
  rw [M7.ResiduePrefix.gcd_union]
  exact Nat.gcd_dvd_left N ((A ∪ B).gcd id)
