import FrozenTarget_b91cd5112b7c9a99
theorem M7.CompactCorrectness.run_disjoint : QuantumHarnessFrozenTarget := by
  intro N inst w E hE bases fuel root hgood hroot
  classical
  induction fuel generalizing bases root with
  | zero =>
      intro e he
      simpa [M7.CompactGeneration.run] using he
  | succ fuel ih =>
      intro e he
      by_cases hstop : root ≤ 0
      · have hs := (M7.CompactGeneration.stop N w E bases (fuel + 1) root hstop).1
        rw [hs] at he
        simp at he
      · have hpos : 0 < M7.RecoveryInstance.count w E bases [] := by
          change 0 < M7.CompactGeneration.residual w E bases []
          rw [← hroot]
          omega
        have hins := M7.RecoveryInstance.insert_good N w E bases hE hgood hpos
        have hgood' : M7.RecoveryInstance.GoodBases w
            (insert (M7.CompactGeneration.emission w E bases).representative bases) := by
          exact hins.1
        have hfresh : (M7.CompactGeneration.emission w E bases).representative ∉ bases := by
          exact hins.2
        simp only [M7.CompactGeneration.run, if_neg hstop, List.mem_cons] at he
        rcases he with he | he
        · subst e
          exact hfresh
        · have hdis := ih (insert (M7.CompactGeneration.emission w E bases).representative bases)
            _ hgood' rfl e he
          intro hb
          exact hdis (Finset.mem_insert_of_mem hb)
