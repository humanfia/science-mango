import M5CRT

theorem M5.CRT.safe_prime_residue : ∀ p δ T e : ℕ, p.Prime → p ∣ δ → Nat.gcd (Nat.gcd T δ) e = 1 → ¬ p ∣ e + M5.CRT.repairResidue e p * T := by
  change ∀ p δ T e : ℕ, p.Prime → p ∣ δ → Nat.gcd (Nat.gcd T δ) e = 1 → ¬ p ∣ e + M5.CRT.repairResidue e p * T
  intro p δ T e hp hδ hg
  by_cases he : p ∣ e
  · intro h
    have hsum : p ∣ e + T := by
      simpa [M5.CRT.repairResidue, he] using h
    have hT : p ∣ T := (Nat.dvd_add_right he).mp hsum
    have hd : p ∣ Nat.gcd (Nat.gcd T δ) e :=
      Nat.dvd_gcd (Nat.dvd_gcd hT hδ) he
    rw [hg] at hd
    exact hp.not_dvd_one hd
  · simpa [M5.CRT.repairResidue, he] using he
def QuantumHarnessFrozenTarget : Prop :=
  ∀ δ T e k : ℕ, 0 < δ → Nat.gcd (Nat.gcd T δ) e = 1 → (∀ p ∈ δ.primeFactors, Nat.ModEq p k (M5.CRT.repairResidue e p)) → Nat.gcd δ (e + k * T) = 1
