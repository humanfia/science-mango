import M5QuotientMonomialPeriod
import M5RepairSupport

theorem M5.RepairSupport.replacement_anchor : ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q
  intro A e q he h0
  simp [M5.RepairSupport.repaired, he, Ne.symm he, h0]

theorem M5.RepairSupport.replacement_card : ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card
  intro A e q he hq
  change (insert q (A.erase e)).card = A.card
  have hq' : q ∉ A.erase e := fun h => hq (Finset.mem_erase.mp h).2
  rw [Finset.card_insert_of_notMem hq', Finset.card_erase_of_mem he]
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨e, he⟩
  omega

theorem M5.RepairSupport.replacement_combined_gcd : ∀ (A B : Finset ℕ) (e q : ℕ), M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) := by
  intro A B e q
  unfold M5.RepairSupport.combinedGcd M5.RepairSupport.repaired
  rw [Finset.gcd_insert]
  change Nat.gcd (Nat.gcd q ((A.erase e).gcd id)) (B.gcd id) = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id))
  exact Nat.gcd_assoc q ((A.erase e).gcd id) (B.gcd id)

theorem M5.RepairSupport.replacement_polynomial_residue : ∀ (A : Finset ℕ) (e k T : ℕ), e ∈ A → e + k * T ∉ A → AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.RepairSupport.repaired A e (e + k * T))) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport A) := by
  intro A e k T he hf
  classical
  have hf' : e + k * T ∉ A.erase e := by
    intro h
    exact hf (Finset.mem_of_mem_erase h)
  unfold M5.RepairSupport.repaired M5.SupportPolynomial.ofSupport
  rw [Finset.sum_insert hf']
  conv_rhs =>
    rw [← Finset.insert_erase he, Finset.sum_insert (Finset.notMem_erase e A)]
  rw [map_add, map_add]
  congr 1
  first
  | apply M5.quotient_monomial_period
  | apply M5.SupportPolynomial.quotient_monomial_period
  | simpa only [Polynomial.monomial_one] using
      (M5.quotient_monomial_period (T := T) (a := e) (j := k))

theorem M5.RepairSupport.replacement_range : ∀ (A : Finset ℕ) (e q L : ℕ), (∀ a ∈ A, a < L) → q < L → ∀ a ∈ M5.RepairSupport.repaired A e q, a < L := by
  change ∀ (A : Finset ℕ) (e q L : ℕ), (∀ a ∈ A, a < L) → q < L → ∀ a ∈ M5.RepairSupport.repaired A e q, a < L
  intro A e q L hA hq a ha
  change a ∈ insert q (A.erase e) at ha
  rcases Finset.mem_insert.mp ha with h | h
  · subst a
    exact hq
  · exact hA a (Finset.mem_of_mem_erase h)

theorem M5.RepairSupport.replacement_connected : ∀ (A B : Finset ℕ) (e q : ℕ), Nat.gcd (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) q = 1 → M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = 1 := by
  intro A B e q h
  rw [M5.RepairSupport.replacement_combined_gcd, Nat.gcd_comm q]
  exact h
#print axioms M5.RepairSupport.replacement_anchor
#print axioms M5.RepairSupport.replacement_card
#print axioms M5.RepairSupport.replacement_combined_gcd
#print axioms M5.RepairSupport.replacement_connected
#print axioms M5.RepairSupport.replacement_polynomial_residue
#print axioms M5.RepairSupport.replacement_range
