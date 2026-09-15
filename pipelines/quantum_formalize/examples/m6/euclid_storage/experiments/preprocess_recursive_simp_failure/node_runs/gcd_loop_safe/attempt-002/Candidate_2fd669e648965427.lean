import FrozenTarget_2fd669e648965427
theorem M6.EuclidStorage.gcd_loop_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c e t width hwidth hs hw hf hc he ht
      simp [M6.Euclid.euclidAux] at hc he ht
      simp [M6.EuclidStorage.gcdSafe]
      simp only [M6.EuclidStorage.slotsFit] at hs ⊢
      repeat' constructor <;> omega
  | succ fuel ih =>
      intro s c e t width hwidth hs hw hf hc he ht
      by_cases hq : s.q = 0
      · simp [M6.Euclid.euclidAux, hq] at hc he ht
        simp [M6.EuclidStorage.gcdSafe, hq]
        simp only [M6.EuclidStorage.slotsFit] at hs ⊢
        repeat' constructor <;> omega
      · have hrem := M6.Euclid.remainder_aux_correct
          (M6.Euclid.rank s.p) s.p s.q (le_refl _)
        have hpasses := M6.Euclid.remainder_passes
          (M6.Euclid.rank s.p) s.p s.q
        have hcorrect := M6.Euclid.remainder_correct s.p s.q
        have hzero : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
          simp [M6.Euclid.rank]
        have href (a b : ℕ) := M6.EuclidStorage.rem_loop_refines
          (M6.Euclid.rank s.p) { s with work := s.p } a b
        have rp (a b : ℕ) := (href a b).1
        have rq (a b : ℕ) := (href a b).2.1
        have rs (a b : ℕ) := (href a b).2.2.1
        have rwk (a b : ℕ) := (href a b).2.2.2.1
        have rc (a b : ℕ) := (href a b).2.2.2.2.1
        have re (a b : ℕ) := (href a b).2.2.2.2.2.1
        have rt (a b : ℕ) := (href a b).2.2.2.2.2.2
        simp only [M6.Euclid.euclidAux, hq, ite_false] at hc he ht
        simp only [M6.Euclid.remainder] at hc he ht hcorrect
        simp only [M6.EuclidStorage.gcdSafe, hq, ite_false]
        simp only [rp, rq, rs, rwk, rc, re, rt, M6.Euclid.remainder]
        try dsimp only
        repeat' first
          | assumption
          | apply And.intro
          | apply ih
          | apply M6.EuclidStorage.rem_loop_safe
        all_goals
          simp only [M6.EuclidStorage.slotsFit, M6.Euclid.remainder,
            hzero] at *
          try dsimp only at *
          repeat' constructor <;> first | assumption | omega
