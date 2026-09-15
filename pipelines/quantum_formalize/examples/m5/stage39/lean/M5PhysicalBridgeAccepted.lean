import M5PhysicalBridge

theorem M5.PhysicalBridge.packed_divisibility : ∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val) := by
  change ∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val)
  intro w T d r hd
  have ht : T % d = 0 := Nat.mod_eq_zero_of_dvd hd
  simp [M5.Packing.packedSupport, M5.Packing.packedValue,
    Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, ht]

theorem M5.PhysicalBridge.positive_member : ∀ A : Finset ℕ, 2 ≤ A.card → 0 ∈ A → ∃ a ∈ A, 0 < a := by
  change ∀ A : Finset ℕ, 2 ≤ A.card → 0 ∈ A → ∃ a ∈ A, 0 < a
  intro A hcard hzero
  by_contra h
  have hsub : A ⊆ {0} := by
    intro a ha
    have haz : a = 0 := by
      by_contra hne
      exact h ⟨a, ha, Nat.pos_of_ne_zero hne⟩
    simpa only [Finset.mem_singleton] using haz
  have hle : A.card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  omega

theorem M5.PhysicalBridge.remaining_gcd_feasible : ∀ (T : ℕ) (A B : Finset ℕ) (e : ℕ), e ∈ A → M5.Connectivity.supportGcd T A B = 1 → Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd A B e)) e = 1 := by
  change ∀ (T : ℕ) (A B : Finset ℕ) (e : ℕ), e ∈ A → M5.Connectivity.supportGcd T A B = 1 → Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd A B e)) e = 1
  intro T A B e he h
  have hA : A.gcd id = Nat.gcd e ((A.erase e).gcd id) := by
    calc
      A.gcd id = (insert e (A.erase e)).gcd id :=
        congrArg (fun s : Finset ℕ => s.gcd id) (Finset.insert_erase he).symm
      _ = Nat.gcd e ((A.erase e).gcd id) := by
        exact Finset.gcd_insert
  unfold M5.Connectivity.supportGcd at h
  unfold M5.PhysicalBridge.remainingGcd
  rw [hA] at h
  simpa only [Nat.gcd_assoc, Nat.gcd_comm, Nat.gcd_left_comm] using h

theorem M5.PhysicalBridge.repaired_exponent_cutoff : ∀ w T e δ k : ℕ, 0 < T → e < w * T → δ < w * T → k < w + δ → e + k * T < M5.packingCutoff w T := by
  change ∀ w T e δ k : ℕ, 0 < T → e < w * T → δ < w * T → k < w + δ → e + k * T < M5.packingCutoff w T
  intro w T e δ k hT he hδ hk
  have hk_bound : k + 2 ≤ w + w * T := by omega
  have hprod := Nat.mul_le_mul_right T hk_bound
  unfold M5.packingCutoff
  nlinarith

theorem M5.PhysicalBridge.packed_combined_gcd : ∀ (w T : ℕ) (r s : Fin w → Fin T), M5.Connectivity.supportGcd T (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) = Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => (r i).val)) (Finset.univ.gcd (fun i : Fin w => (s i).val))) := by
  change ∀ (w T : ℕ) (r s : Fin w → Fin T), M5.Connectivity.supportGcd T (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) = Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => (r i).val)) (Finset.univ.gcd (fun i : Fin w => (s i).val)))
  intro w T r s
  have h : ∀ d : ℕ, d ∣ M5.Connectivity.supportGcd T (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) ↔ d ∣ Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => (r i).val)) (Finset.univ.gcd (fun i : Fin w => (s i).val))) := by
    intro d
    by_cases hd : d ∣ T <;>
      simp [M5.Connectivity.support_gcd_dvd, Nat.dvd_gcd_iff,
        Finset.dvd_gcd_iff, M5.PhysicalBridge.packed_divisibility, hd]
  exact Nat.dvd_antisymm ((h _).mp (dvd_refl _)) ((h _).mpr (dvd_refl _))

theorem M5.PhysicalBridge.remaining_gcd_bounds : ∀ (A B : Finset ℕ) (e K : ℕ), 2 ≤ B.card → 0 ∈ B → (∀ b ∈ B, b < K) → 0 < M5.PhysicalBridge.remainingGcd A B e ∧ M5.PhysicalBridge.remainingGcd A B e < K := by
  change ∀ (A B : Finset ℕ) (e K : ℕ), 2 ≤ B.card → 0 ∈ B → (∀ b ∈ B, b < K) → 0 < M5.PhysicalBridge.remainingGcd A B e ∧ M5.PhysicalBridge.remainingGcd A B e < K
  intro A B e K hcard hzero hbound
  obtain ⟨b, hb, hbpos⟩ := M5.PhysicalBridge.positive_member B hcard hzero
  have hd : M5.PhysicalBridge.remainingGcd A B e ∣ b := by
    unfold M5.PhysicalBridge.remainingGcd
    exact dvd_trans (Nat.gcd_dvd_right _ _) (Finset.gcd_dvd hb)
  have hpos : 0 < M5.PhysicalBridge.remainingGcd A B e := by
    by_contra h
    have hz : M5.PhysicalBridge.remainingGcd A B e = 0 := by omega
    rw [hz] at hd
    simp only [zero_dvd_iff] at hd
    omega
  exact ⟨hpos, lt_of_le_of_lt (Nat.le_of_dvd hbpos hd) (hbound b hb)⟩
#print axioms M5.PhysicalBridge.packed_divisibility
#print axioms M5.PhysicalBridge.packed_combined_gcd
#print axioms M5.PhysicalBridge.positive_member
#print axioms M5.PhysicalBridge.remaining_gcd_bounds
#print axioms M5.PhysicalBridge.remaining_gcd_feasible
#print axioms M5.PhysicalBridge.repaired_exponent_cutoff
