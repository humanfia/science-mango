import FrozenTarget_f3a3f882a6dad142
theorem M5.CRT.bounded_connectivity_repair : QuantumHarnessFrozenTarget := by
  change ∀ δ T e w : ℕ, 0 < δ → 0 < T → Nat.gcd (Nat.gcd T δ) e = 1 → ∃ k : ℕ, w ≤ k ∧ k < w + δ ∧ Nat.gcd δ (e + k * T) = 1
  intro δ T e w hδ hT hg
  obtain ⟨r, hrlt, hr⟩ := M5.CRT.prime_crt_representative δ e hδ
  obtain ⟨k, hwk, hklt, hkr⟩ := M5.CRT.interval_representative δ r w hδ
  refine ⟨k, hwk, hklt, ?_⟩
  apply M5.CRT.residues_force_coprime δ T e k hδ hg
  intro p hp
  have hpδ : p ∣ δ := (Nat.mem_primeFactors.mp hp).2.1
  have hkp : Nat.ModEq p k r := by
    first
    | exact Nat.ModEq.of_dvd hpδ hkr
    | exact hkr.of_dvd hpδ
  exact hkp.trans (hr p hp)
