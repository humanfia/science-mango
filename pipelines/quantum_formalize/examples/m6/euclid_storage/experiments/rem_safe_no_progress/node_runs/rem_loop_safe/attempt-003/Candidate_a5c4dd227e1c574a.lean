import FrozenTarget_a5c4dd227e1c574a
theorem M6.EuclidStorage.rem_loop_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t width hwidth hs hf hc ht
      simp only [M6.Euclid.remainderAux] at hc ht
      simp only [M6.EuclidStorage.remSafe]
      aesop (add safe tactic omega)
  | succ fuel ih =>
      intro s c t width hwidth hs hf hc ht
      by_cases hw : s.work = 0
      · simp [M6.Euclid.remainderAux, hw] at hc ht
        simp [M6.EuclidStorage.remSafe, hw]
        aesop (add safe tactic omega)
      · by_cases hq : s.q = 0
        · simp [M6.Euclid.remainderAux, hw, hq] at hc ht
          simp [M6.EuclidStorage.remSafe, hw, hq]
          aesop (add safe tactic omega)
        · by_cases hd : s.work.degree < s.q.degree
          · simp [M6.Euclid.remainderAux, hw, hq, hd, not_le_of_gt hd] at hc ht
            simp [M6.EuclidStorage.remSafe, hw, hq, hd, not_le_of_gt hd]
            aesop (add safe tactic omega)
          · have hle : s.q.degree ≤ s.work.degree := le_of_not_gt hd
            have hdrop := M6.Euclid.cancel_drop s.work s.q hw hq hle
            have hs' : M6.EuclidStorage.slotsFit width
                { s with work := M6.Euclid.cancel s.work s.q } := by
              simp only [M6.EuclidStorage.slotsFit] at hs ⊢
              rcases hs with ⟨h1, h2, h3, h4⟩
              repeat' constructor <;> omega
            have hc' : c + 1 + (M6.Euclid.remainderAux fuel
                (M6.Euclid.cancel s.work s.q) s.q).cancellations ≤ 32 * width := by
              simpa [M6.Euclid.remainderAux, hw, hq, hd, hle,
                Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc
            have ht' : t + 2 + (M6.Euclid.remainderAux fuel
                (M6.Euclid.cancel s.work s.q) s.q).passes ≤ 32 * width := by
              simpa [M6.Euclid.remainderAux, hw, hq, hd, hle,
                Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht
            have hr := ih { s with work := M6.Euclid.cancel s.work s.q }
              (c + 1) (t + 2) width hwidth hs' (by omega) hc' ht'
            simp only [M6.EuclidStorage.remSafe]
            simp only [hw, hq, hd, hle, ite_true, ite_false, false_or,
              or_false, false_and, and_false, true_and, and_true, not_false_eq_true]
            aesop (add safe tactic omega)
