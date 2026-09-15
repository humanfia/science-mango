import FrozenTarget_71a42f05d0e337c9
theorem M7.ResiduePrefix.gcd_union : QuantumHarnessFrozenTarget := by
  intro N A B
  change Nat.gcd N (Nat.gcd (A.gcd id) (B.gcd id)) = Nat.gcd N ((A ∪ B).gcd id)
  rw [Finset.gcd_union]
