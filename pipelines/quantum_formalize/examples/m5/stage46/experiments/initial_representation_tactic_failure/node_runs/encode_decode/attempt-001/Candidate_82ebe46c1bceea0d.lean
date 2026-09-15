import FrozenTarget_82ebe46c1bceea0d
theorem M5.PhysicalRecovery.encode_decode : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (q : List Bool), 0 < N → q.length = M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) = q
  intro N q hN hq
  classical
  have hmem (offset j : ℕ) (hj : j < N - 1) (hjq : offset + j < q.length) :
      decide (j + 1 ∈ M5.PhysicalRecovery.selected N offset q) = q[offset + j] := by
    cases hb : q[offset + j] <;>
      simp [M5.PhysicalRecovery.selected, Finset.mem_image, List.getD,
        List.getElem?_eq_getElem, Nat.add_comm, hj, hjq, hb]
  apply List.ext_getElem
  · simp [M5.PhysicalRecovery.encode, hq]
  · intro i hi hiq
    have hic : i < M5.PhysicalRecovery.decisionCount N := by
      simpa [M5.PhysicalRecovery.encode] using hi
    simp only [M5.PhysicalRecovery.encode, List.getElem_ofFn]
    by_cases hleft : i < N - 1
    · simpa [hleft, M5.PhysicalRecovery.selectedA] using
        hmem 0 i hleft (by simpa using hiq)
    · have hj : i - (N - 1) < N - 1 := by
        unfold M5.PhysicalRecovery.decisionCount at hic
        omega
      have he : N - 1 + (i - (N - 1)) = i := by omega
      simpa [hleft, M5.PhysicalRecovery.selectedB, he] using
        hmem (N - 1) (i - (N - 1)) hj (by omega)
