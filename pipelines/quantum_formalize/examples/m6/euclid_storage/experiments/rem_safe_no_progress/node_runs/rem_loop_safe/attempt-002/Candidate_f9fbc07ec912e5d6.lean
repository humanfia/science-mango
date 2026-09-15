import FrozenTarget_f9fbc07ec912e5d6
theorem M6.EuclidStorage.rem_loop_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t width hw hs hf hc ht
      simp [M6.Euclid.remainderAux] at hc ht
      simp [M6.EuclidStorage.remSafe, hs]
      omega
  | succ fuel ih =>
      intro s c t width hw hs hf hc ht
      by_cases h : s.q = 0 ∨ s.work = 0 ∨ s.work.degree < s.q.degree
      · simp [M6.Euclid.remainderAux, h] at hc ht
        simp [M6.EuclidStorage.remSafe, h, hs, hf]
        omega
      · simp only [M6.Euclid.remainderAux, if_neg h] at hc ht
        have hd : M6.Euclid.rank (M6.Euclid.cancel s.work s.q) <
            M6.Euclid.rank s.work :=
          M6.Euclid.cancel_drop s.work s.q
            (by tauto) (by tauto) (le_of_not_gt (by tauto))
        have hs' : M6.EuclidStorage.slotsFit width
            { s with work := M6.Euclid.cancel s.work s.q } := by
          simp only [M6.EuclidStorage.slotsFit] at hs ⊢
          dsimp
          rcases hs with ⟨h1, h2, h3, h4⟩
          repeat' constructor <;> omega
        have hr := ih { s with work := M6.Euclid.cancel s.work s.q }
          (c + 1) (t + 2) width hw hs' (by omega)
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc)
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht)
        simp [M6.EuclidStorage.remSafe, h, hs, hf, hr]
        omega
