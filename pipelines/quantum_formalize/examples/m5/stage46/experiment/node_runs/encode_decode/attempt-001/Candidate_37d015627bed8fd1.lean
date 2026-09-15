import FrozenTarget_37d015627bed8fd1
theorem M5.PhysicalRecovery.encode_decode : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (q : List Bool), 0 < N → q.length = M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) = q
  intro N q hN hq
  have hmem (offset j : ℕ) (hj : j < N - 1) (hjq : offset + j < q.length) :
      (j + 1 ∈ M5.PhysicalRecovery.selected N offset q) ↔ q[offset + j] = true := by
    cases hb : q[offset + j] <;>
      simp [M5.PhysicalRecovery.selected, Finset.mem_image, List.getD,
        List.getElem?_eq_getElem, Nat.add_comm, hj, hjq, hb]
  apply List.ext_getElem
  · simpa [M5.PhysicalRecovery.encode] using hq.symm
  · intro i hi hiq
    have hic : i < M5.PhysicalRecovery.decisionCount N := by omega
    have hib : i < 2 * (N - 1) := by
      simpa [M5.PhysicalRecovery.decisionCount] using hic
    by_cases hfirst : i < N - 1
    · have hm := hmem 0 i hfirst (by omega)
      simp only [Nat.zero_add] at hm
      cases hb : q[i] <;>
        simp [hb] at hm <;>
        simp [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.selectedA,
          hfirst, hm, hb]
    · have hj : i - (N - 1) < N - 1 := by omega
      have hoff : N - 1 + (i - (N - 1)) = i := by omega
      have hm := hmem (N - 1) (i - (N - 1)) hj (by omega)
      simp only [hoff] at hm
      cases hb : q[i] <;>
        simp [hb] at hm <;>
        simp [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.selectedB,
          hfirst, hm, hb]
