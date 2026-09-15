import M5IntegerMobius

theorem M5.Connectivity.support_gcd_dvd : ∀ (N d : ℕ) (A B : Finset ℕ), d ∣ M5.Connectivity.supportGcd N A B ↔ d ∣ N ∧ (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b) := by
  intro N d A B
  simp [M5.Connectivity.supportGcd, Nat.dvd_gcd_iff, Finset.dvd_gcd_iff, and_assoc]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → N.divisors.filter (fun d => (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b)) = (M5.Connectivity.supportGcd N A B).divisors
