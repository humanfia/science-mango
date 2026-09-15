import FrozenTarget_68c767ab106187d7
theorem M6.EuclidStorage.rem_loop_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t width hw hs hf hc ht
      simp only [M6.Euclid.remainderAux] at hc ht
      simp only [M6.EuclidStorage.remSafe]
      repeat' constructor <;> first | assumption | omega
  | succ fuel ih =>
      intro s c t width hw hs hf hc ht
      simp only [M6.EuclidStorage.remSafe]
      split
      all_goals
        simp_all only [M6.Euclid.remainderAux, ↓reduceIte]
        first
        | solve | repeat' constructor <;> first | assumption | omega
        | skip
      all_goals
        have hd : M6.Euclid.rank (M6.Euclid.cancel s.work s.q) <
            M6.Euclid.rank s.work := by
          apply M6.Euclid.cancel_drop
          · tauto
          · tauto
          · first | tauto | exact le_of_not_gt (by tauto)
        have hs' : M6.EuclidStorage.slotsFit width
            { s with work := M6.Euclid.cancel s.work s.q } := by
          simp only [M6.EuclidStorage.slotsFit] at hs ⊢
          repeat' constructor <;> omega
        have hr := ih { s with work := M6.Euclid.cancel s.work s.q }
          (c + 1) (t + 2) width hw hs' (by omega) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht)
        repeat' constructor <;> first | assumption | omega
