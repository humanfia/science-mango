import M5QuotientMonomialPeriod
import M5RepairSupport

theorem M5.RepairSupport.replacement_anchor : ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q
  intro A e q he hA
  simp [M5.RepairSupport.repaired, he, Ne.symm he, hA]

theorem M5.RepairSupport.replacement_card : ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card
  intro A e q he hq
  change (insert q (A.erase e)).card = A.card
  have hq' : q ∉ A.erase e := by
    intro h
    exact hq (Finset.mem_erase.mp h).2
  rw [Finset.card_insert_of_notMem hq', Finset.card_erase_of_mem he]
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨e, he⟩
  omega

theorem M5.RepairSupport.replacement_combined_gcd : ∀ (A B : Finset ℕ) (e q : ℕ), M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) := by
  intro A B e q
  unfold M5.RepairSupport.combinedGcd M5.RepairSupport.repaired
  rw [Finset.gcd_insert]
  change Nat.gcd (Nat.gcd q ((A.erase e).gcd id)) (B.gcd id) = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id))
  exact Nat.gcd_assoc q ((A.erase e).gcd id) (B.gcd id)

theorem M5.RepairSupport.replacement_connected : ∀ (A B : Finset ℕ) (e q : ℕ), Nat.gcd (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) q = 1 → M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = 1 := by
  intro A B e q h
  rw [M5.RepairSupport.replacement_combined_gcd]
  rw [Nat.gcd_comm q]
  exact h
#print axioms M5.RepairSupport.replacement_anchor
#print axioms M5.RepairSupport.replacement_card
#print axioms M5.RepairSupport.replacement_combined_gcd
#print axioms M5.RepairSupport.replacement_connected
