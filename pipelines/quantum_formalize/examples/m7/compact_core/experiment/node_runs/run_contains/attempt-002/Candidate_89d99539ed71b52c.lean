import FrozenTarget_89d99539ed71b52c
theorem M7.CompactGeneration.run_contains : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero =>
      simpa only [M7.CompactGeneration.run] using (Finset.Subset.refl bases)
  | succ fuel ih =>
      by_cases h : 0 < root
      · simp only [M7.CompactGeneration.run, if_pos h]
        intro x hx
        apply ih (insert (M7.CompactGeneration.emission w E bases).representative bases)
          (M7.CompactGeneration.residual w E
            (insert (M7.CompactGeneration.emission w E bases).representative bases) [])
        exact Finset.mem_insert_of_mem hx
      · simpa only [M7.CompactGeneration.run, if_neg h] using (Finset.Subset.refl bases)
