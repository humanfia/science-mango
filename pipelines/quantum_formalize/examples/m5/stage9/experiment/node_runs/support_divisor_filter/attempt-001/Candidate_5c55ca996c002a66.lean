import FrozenTarget_5c55ca996c002a66
theorem M5.Connectivity.support_divisor_filter : QuantumHarnessFrozenTarget := by
  intro N A B hN
  have hdiv : M5.Connectivity.supportGcd N A B ∣ N :=
    ((M5.Connectivity.support_gcd_dvd N
      (M5.Connectivity.supportGcd N A B) A B).mp dvd_rfl).1
  have hg : M5.Connectivity.supportGcd N A B ≠ 0 := by
    intro hz
    rw [hz] at hdiv
    exact (Nat.ne_of_gt hN) (Nat.zero_dvd.mp hdiv)
  ext d
  simp [Finset.mem_filter, Nat.mem_divisors, Nat.ne_of_gt hN, hg,
    M5.Connectivity.support_gcd_dvd, and_assoc]
