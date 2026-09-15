import FrozenTarget_0c7b375d844b09dc
theorem M7.CompactCorrectness.run_zero : QuantumHarnessFrozenTarget := by
  intro N inst w E hE bases fuel root hb hr hf
  classical
  induction fuel generalizing bases root with
  | zero =>
      have hn := (M7.RecoveryInstance.count_card N w E bases hE hb []).2.2
      have hc : root = M7.RecoveryInstance.count w E bases [] :=
        hr.trans (M7.CompactCorrectness.residual_eq N w E bases [])
      have hz : root = 0 := by omega
      have hs := M7.CompactGeneration.stop N w E bases 0 root (by omega)
      exact ⟨hs.2.2.1.trans hz, hs.2.2.2⟩
  | succ fuel ih =>
      have hc : root = M7.RecoveryInstance.count w E bases [] :=
        hr.trans (M7.CompactCorrectness.residual_eq N w E bases [])
      by_cases hp : 0 < root
      · have hpos : 0 < M7.RecoveryInstance.count w E bases [] := by omega
        have hg := (M7.RecoveryInstance.insert_good N w E bases hE hb hpos).1
        have hd := (M7.RecoveryInstance.strict_decrease N w E bases hE hb hpos).2
        have hbound :
            (M7.CompactGeneration.residual w E
              (M7.RecoveryInstance.insertedBases w E bases) []).toNat ≤ fuel := by
          rw [M7.CompactCorrectness.residual_eq N w E]
          omega
        have hi := ih (M7.RecoveryInstance.insertedBases w E bases)
          (M7.CompactGeneration.residual w E
            (M7.RecoveryInstance.insertedBases w E bases) []) hg rfl hbound
        simpa only [M7.CompactGeneration.run, if_pos hp,
          (M7.CompactCorrectness.emission_eq N w E bases).2] using hi
      · have hn := (M7.RecoveryInstance.count_card N w E bases hE hb []).2.2
        have hz : root = 0 := by omega
        have hs := M7.CompactGeneration.stop N w E bases (fuel + 1) root (by omega)
        exact ⟨hs.2.2.1.trans hz, hs.2.2.2⟩
