import FrozenTarget_57b1016a4a486a22
theorem M7.CompactCorrectness.generate_card : QuantumHarnessFrozenTarget := by
  classical
  intro N inst w E hE
  have hcard : ∀ (fuel : ℕ) (bases : Finset (M7.Action.Recipe N)) (root : ℤ),
      M7.RecoveryInstance.GoodBases w bases →
      root = M7.CompactGeneration.residual w E bases [] →
      (M7.CompactGeneration.run w E fuel bases root).finalBases.card =
        bases.card + (M7.CompactGeneration.run w E fuel bases root).emitted.length := by
    intro fuel
    induction fuel with
    | zero =>
        intro bases root hb hr
        simp [M7.CompactGeneration.run]
    | succ fuel ih =>
        intro bases root hb hr
        by_cases hp : 0 < root
        · have hc : 0 < M7.RecoveryInstance.count w E bases [] := by
            rw [hr, M7.CompactCorrectness.residual_eq] at hp
            exact hp
          have hg := M7.RecoveryInstance.insert_good N w E bases hE hb hc
          have hb' : M7.RecoveryInstance.GoodBases w
              (insert (M7.CompactGeneration.emission w E bases).representative bases) := by
            rw [(M7.CompactCorrectness.emission_eq N w E bases).2]
            exact hg.1
          have hf : (M7.CompactGeneration.emission w E bases).representative ∉ bases := hg.2
          simp only [M7.CompactGeneration.run, if_pos hp, List.length_cons]
          rw [ih _ _ hb' rfl, Finset.card_insert_of_notMem hf]
          omega
        · simp [M7.CompactGeneration.run, hp]
  let root := M7.CompactGeneration.residual (N := N) w E ∅ []
  have h := hcard root.toNat ∅ root (M7.CompactCorrectness.initial N w E hE).1 rfl
  simpa only [M7.CompactGeneration.generate, root, Finset.card_empty, Nat.zero_add] using h
