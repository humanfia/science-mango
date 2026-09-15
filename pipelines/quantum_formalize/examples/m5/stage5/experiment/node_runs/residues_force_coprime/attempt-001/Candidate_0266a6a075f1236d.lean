import FrozenTarget_0266a6a075f1236d
theorem M5.CRT.residues_force_coprime : QuantumHarnessFrozenTarget := by
  change ∀ δ T e k : ℕ, 0 < δ → Nat.gcd (Nat.gcd T δ) e = 1 → (∀ p ∈ δ.primeFactors, Nat.ModEq p k (M5.CRT.repairResidue e p)) → Nat.gcd δ (e + k * T) = 1
  intro δ T e k hδ hg hk
  apply Nat.coprime_of_dvd
  intro p hp hpδ hpe
  have hmem : p ∈ δ.primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hp, hpδ, Nat.ne_of_gt hδ⟩
  have hmod := ((hk p hmem).mul_right T).add_left e
  exact M5.CRT.safe_prime_residue p δ T e hp hpδ hg
    ((hmod.dvd_iff (dvd_refl p)).mp hpe)
