import M5IntegerMobius

theorem M5.Connectivity.divisor_moebius : ∀ n : ℕ, (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0 := by
  change ∀ n : ℕ, (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0
  intro n
  rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius, ArithmeticFunction.one_apply]

theorem M5.Connectivity.support_gcd_dvd : ∀ (N d : ℕ) (A B : Finset ℕ), d ∣ M5.Connectivity.supportGcd N A B ↔ d ∣ N ∧ (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) := by
  intro N d A B
  simp [M5.Connectivity.supportGcd, Nat.dvd_gcd_iff, Finset.dvd_gcd_iff, and_assoc]

theorem M5.Connectivity.support_divisor_filter : ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → N.divisors.filter (fun d => (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b)) = (M5.Connectivity.supportGcd N A B).divisors := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → (∑ d ∈ N.divisors, if (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) then ArithmeticFunction.moebius d else 0) = if M5.Connectivity.supportGcd N A B = 1 then (1 : ℤ) else 0
