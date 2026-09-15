import FrozenTarget_ccd311414da6bbc1
theorem M7.GenerationCalls.run_count : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).2.root = (M7.GenerationCalls.runMeasured w E fuel bases root).1.emitted.length + 1 ∧ (M7.GenerationCalls.runMeasured w E fuel bases root).2.children = 2 * M7.PrefixBits.depth N * (M7.GenerationCalls.runMeasured w E fuel bases root).1.emitted.length
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero => simp [M7.GenerationCalls.runMeasured]
  | succ fuel ih =>
      by_cases h : 0 < root
      · obtain ⟨hr, hc⟩ := ih
          (insert (M7.GenerationCalls.emissionMeasured w E bases).1.representative bases)
          (M7.CompactGeneration.residual w E
            (insert (M7.GenerationCalls.emissionMeasured w E bases).1.representative bases) [])
        simp only [M7.GenerationCalls.runMeasured, if_pos h, List.length_cons]
        simp [hr, hc, M7.GenerationCalls.emission_count, Nat.mul_add,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      · simp [M7.GenerationCalls.runMeasured, h]
