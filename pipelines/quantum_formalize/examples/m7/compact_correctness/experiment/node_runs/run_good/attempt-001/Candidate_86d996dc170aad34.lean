import FrozenTarget_86d996dc170aad34
theorem M7.CompactCorrectness.run_good : QuantumHarnessFrozenTarget := by
  intro N inst w E hE bases fuel root hgood hroot
  induction fuel generalizing bases root with
  | zero =>
      simpa [M7.CompactGeneration.run] using hgood
  | succ fuel ih =>
      simp only [M7.CompactGeneration.run]
      split
      all_goals first
      | exact hgood
      | have hpos : 0 < M7.RecoveryInstance.count w E bases [] := by
          change 0 < M7.CompactGeneration.residual w E bases []
          omega
        have hins := (M7.RecoveryInstance.insert_good N w E bases hE hgood hpos).1
        apply ih
        · change M7.RecoveryInstance.GoodBases w (M7.RecoveryInstance.insertedBases w E bases)
          exact hins
        · rfl
