import FrozenTarget_0f7c4c3aa3432b73
theorem M5.PhysicalRecovery.encode_decode : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (q : List Bool), 0 < N → q.length = M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) = q
  intro N q hN hq
  have hmem (offset j : ℕ) (hj : j < N - 1) (hjq : offset + j < q.length) :
      decide (j + 1 ∈ M5.PhysicalRecovery.selected N offset q) = q[offset + j] := by
    cases hb : q[offset + j] <;>
      simp [M5.PhysicalRecovery.selected, Finset.mem_image, List.getD,
        List.getElem?_eq_getElem, Nat.add_comm, hj, hjq, hb]
  apply List.ext_getElem
  · simp [M5.PhysicalRecovery.encode, hq]
  · intro i hi hiq
    have hib : i < M5.PhysicalRecovery.decisionCount N := by omega
    simp only [M5.PhysicalRecovery.decisionCount] at hib
    by_cases hleft : i < N - 1
    · have hm := hmem 0 i hleft (by omega)
      cases hb : q[i] <;>
        simpa [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.selectedA,
          M5.PhysicalRecovery.selectedB, hleft, hb] using hm
    · have hj : i - (N - 1) < N - 1 := by omega
      have he : N - 1 + (i - (N - 1)) = i := by omega
      have hm := hmem (N - 1) (i - (N - 1)) hj (by omega)
      cases hb : q[i] <;>
        simpa [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.selectedA,
          M5.PhysicalRecovery.selectedB, hleft, he, hb] using hm
