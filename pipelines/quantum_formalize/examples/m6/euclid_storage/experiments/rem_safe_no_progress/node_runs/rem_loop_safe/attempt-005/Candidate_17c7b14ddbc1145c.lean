import FrozenTarget_17c7b14ddbc1145c
theorem M6.EuclidStorage.rem_loop_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t width hwidth hfit hfuel hc ht
      simp only [M6.Euclid.remainderAux] at hc ht
      simp only [M6.EuclidStorage.remSafe]
      exact ⟨hfit, by omega, by omega, by omega⟩
  | succ fuel ih =>
      intro s c t width hwidth hfit hfuel hc ht
      by_cases hw : s.work = 0
      · simp_all [M6.EuclidStorage.remSafe, M6.Euclid.remainderAux] <;> omega
      by_cases hq : s.q = 0
      · simp_all [M6.EuclidStorage.remSafe, M6.Euclid.remainderAux] <;> omega
      by_cases hd : s.q.degree ≤ s.work.degree
      · have hdrop := M6.Euclid.cancel_drop s.work s.q hw hq hd
        have hfit' : M6.EuclidStorage.slotsFit width
            { s with work := M6.Euclid.cancel s.work s.q } := by
          simp only [M6.EuclidStorage.slotsFit] at hfit ⊢
          try dsimp only
          omega
        have hnlt : ¬ s.work.degree < s.q.degree := not_lt.mpr hd
        simp only [M6.Euclid.remainderAux, hw, hq, hd, hnlt,
          ite_true, ite_false, false_or, or_false] at hc ht
        have hrec := ih { s with work := M6.Euclid.cancel s.work s.q }
          (c + 1) (t + 2) width hwidth hfit' (by omega)
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc)
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht)
        simp_all [M6.EuclidStorage.remSafe] <;> omega
      · have hlt : s.work.degree < s.q.degree := lt_of_not_ge hd
        simp_all [M6.EuclidStorage.remSafe, M6.Euclid.remainderAux] <;> omega
