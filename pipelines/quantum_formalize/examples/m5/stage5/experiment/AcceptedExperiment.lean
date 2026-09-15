import M5CRT

theorem M5.CRT.interval_representative : ∀ R r w : ℕ, 0 < R → ∃ k : ℕ, w ≤ k ∧ k < w + R ∧ Nat.ModEq R k r := by
  change ∀ R r w : ℕ, 0 < R → ∃ k : ℕ, w ≤ k ∧ k < w + R ∧ Nat.ModEq R k r
  intro R r w hR
  cases R with
  | zero => omega
  | succ n =>
    refine ⟨w + (r + n * w) % (n + 1), by omega, ?_, ?_⟩
    · exact Nat.add_lt_add_left (Nat.mod_lt _ (by omega)) w
    · change (w + (r + n * w) % (n + 1)) % (n + 1) = r % (n + 1)
      calc
        (w + (r + n * w) % (n + 1)) % (n + 1) =
            (w + (r + n * w)) % (n + 1) := by
              simp only [Nat.add_mod, Nat.mod_mod]
        _ = (r + (n + 1) * w) % (n + 1) := by
              congr 1 <;> ring
        _ = r % (n + 1) := by simp [Nat.add_mod]

theorem M5.CRT.prime_crt_representative : ∀ δ e : ℕ, 0 < δ → ∃ r : ℕ, r < M5.CRT.primeProduct δ ∧ ∀ p ∈ δ.primeFactors, Nat.ModEq p r (M5.CRT.repairResidue e p) := by
  change ∀ δ e : ℕ, 0 < δ → ∃ r : ℕ, r < M5.CRT.primeProduct δ ∧ ∀ p ∈ δ.primeFactors, Nat.ModEq p r (M5.CRT.repairResidue e p)
  intro δ e hδ
  have hn : ∀ p ∈ δ.primeFactors, (fun p : ℕ => p) p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hc : Set.Pairwise (↑δ.primeFactors : Set ℕ) (fun p q => Nat.Coprime p q) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).2 hpq
  refine ⟨(Nat.chineseRemainderOfFinset (M5.CRT.repairResidue e) (fun p : ℕ => p) δ.primeFactors hn hc).val, ?_, ?_⟩
  · simpa [M5.CRT.primeProduct] using Nat.chineseRemainderOfFinset_lt_prod (M5.CRT.repairResidue e) (fun p : ℕ => p) hn hc
  · exact (Nat.chineseRemainderOfFinset (M5.CRT.repairResidue e) (fun p : ℕ => p) δ.primeFactors hn hc).property

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

theorem M5.CRT.residues_force_coprime : ∀ δ T e k : ℕ, 0 < δ → Nat.gcd (Nat.gcd T δ) e = 1 → (∀ p ∈ δ.primeFactors, Nat.ModEq p k (M5.CRT.repairResidue e p)) → Nat.gcd δ (e + k * T) = 1 := by
  change ∀ δ T e k : ℕ, 0 < δ → Nat.gcd (Nat.gcd T δ) e = 1 → (∀ p ∈ δ.primeFactors, Nat.ModEq p k (M5.CRT.repairResidue e p)) → Nat.gcd δ (e + k * T) = 1
  intro δ T e k hδ hg hk
  apply Nat.coprime_of_dvd
  intro p hp hpδ hpe
  have hmem : p ∈ δ.primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hp, hpδ, Nat.ne_of_gt hδ⟩
  have hmod := ((hk p hmem).mul_right T).add_left e
  exact M5.CRT.safe_prime_residue p δ T e hp hpδ hg
    ((hmod.dvd_iff (dvd_refl p)).mp hpe)

theorem M5.CRT.bounded_connectivity_repair : ∀ δ T e w : ℕ, 0 < δ → 0 < T → Nat.gcd (Nat.gcd T δ) e = 1 → ∃ k : ℕ, w ≤ k ∧ k < w + δ ∧ Nat.gcd δ (e + k * T) = 1 := by
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
#print axioms M5.CRT.interval_representative
#print axioms M5.CRT.prime_crt_representative
#print axioms M5.CRT.safe_prime_residue
#print axioms M5.CRT.residues_force_coprime
#print axioms M5.CRT.bounded_connectivity_repair
