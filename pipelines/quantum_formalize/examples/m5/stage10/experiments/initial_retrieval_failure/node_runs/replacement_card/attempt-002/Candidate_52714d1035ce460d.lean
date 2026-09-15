import FrozenTarget_52714d1035ce460d
theorem M5.RepairSupport.replacement_card : QuantumHarnessFrozenTarget := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card
  intro A e q he hq
  change (insert q (A.erase e)).card = A.card
  have hq' : q ∉ A.erase e := by
    intro h
    exact hq (Finset.mem_erase.mp h).2
  rw [Finset.card_insert_of_notMem hq', Finset.card_erase_of_mem he]
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨e, he⟩
  omega
