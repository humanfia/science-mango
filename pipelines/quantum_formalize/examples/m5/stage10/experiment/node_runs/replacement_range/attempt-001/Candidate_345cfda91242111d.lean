import FrozenTarget_345cfda91242111d
theorem M5.RepairSupport.replacement_range : QuantumHarnessFrozenTarget := by
  change ∀ (A : Finset ℕ) (e q L : ℕ), (∀ a ∈ A, a < L) → q < L → ∀ a ∈ M5.RepairSupport.repaired A e q, a < L
  intro A e q L hA hq a ha
  change a ∈ insert q (A.erase e) at ha
  rcases Finset.mem_insert.mp ha with h | h
  · subst a
    exact hq
  · exact hA a (Finset.mem_of_mem_erase h)
