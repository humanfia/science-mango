import FrozenTarget_a10974b1042a920d
theorem M7.CompactCorrectness.run_leaves : QuantumHarnessFrozenTarget := by
  intro N inst w E hE bases fuel root hgood hroot
  induction fuel generalizing bases root with
  | zero =>
      intro e he
      simpa [M7.CompactGeneration.run] using he
  | succ fuel ih =>
      intro e he
      by_cases hp : 0 < root
      · have hc : 0 < M7.RecoveryInstance.count w E bases [] := by
          simpa only [hroot, M7.CompactCorrectness.residual_eq] using hp
        simp only [M7.CompactGeneration.run, if_pos hp,
          if_neg (not_le.mpr hp), List.mem_cons] at he
        rcases he with he | he
        · subst e
          rw [(M7.CompactCorrectness.emission_eq N w E bases).1]
          exact M7.RecoveryPrefix.completed_subroot N w E _
            (M7.RecoveryInstance.fresh_leaf N w E bases hE hgood hc).2
        · apply ih _ _ ?_ rfl e he
          rw [(M7.CompactCorrectness.emission_eq N w E bases).2]
          exact (M7.RecoveryInstance.insert_good N w E bases hE hgood hc).1
      · simpa [M7.CompactGeneration.run, hp, le_of_not_gt hp] using he
