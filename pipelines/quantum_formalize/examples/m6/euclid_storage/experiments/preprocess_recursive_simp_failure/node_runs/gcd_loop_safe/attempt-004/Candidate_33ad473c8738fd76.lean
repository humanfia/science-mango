import FrozenTarget_33ad473c8738fd76
theorem M6.EuclidStorage.gcd_loop_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c e t width hwidth hs hw hf hc he ht
      simp only [M6.Euclid.euclidAux] at hc he ht
      simp only [M6.EuclidStorage.gcdSafe, M6.EuclidStorage.slotsFit] at hs ⊢
      repeat' constructor <;> omega
  | succ fuel ih =>
      intro s c e t width hwidth hs hw hf hc he ht
      by_cases hq : s.q = 0
      · simp [M6.Euclid.euclidAux, hq] at hc he ht
        simp [M6.EuclidStorage.gcdSafe, hq]
        simp only [M6.EuclidStorage.slotsFit] at hs ⊢
        repeat' constructor <;> omega
      · have ha := M6.Euclid.remainder_aux_correct
          (M6.Euclid.rank s.p) s.p s.q (le_refl _)
        have hb := M6.Euclid.remainder_passes
          (M6.Euclid.rank s.p) s.p s.q
        have hd := M6.Euclid.remainder_correct s.p s.q
        have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
          simp [M6.Euclid.rank]
        simp only [M6.Euclid.euclidAux, hq, ite_false] at hc he ht
        simp only [M6.Euclid.remainder] at hc he ht hd
        simp only [M6.EuclidStorage.gcdSafe, hq, ite_false]
        try dsimp only
        match goal with
        | |- context [M6.EuclidStorage.remLoop ?f ?ss ?cc ?tt] =>
            obtain ⟨hp', hq', hs', hw', hc', he', ht'⟩ :=
              M6.EuclidStorage.rem_loop_refines f ss cc tt
            simp only [hp', hq', hs', hw', hc', he', ht']
        try dsimp only
        simp only [M6.EuclidStorage.slotsFit] at hs
        repeat' apply And.intro
        all_goals first
          | (apply M6.EuclidStorage.rem_loop_safe <;>
              first
              | assumption
              | (simp only [M6.EuclidStorage.slotsFit] at ⊢
                 dsimp only
                 repeat' apply And.intro
                 all_goals omega))
          | (apply ih <;>
              first
              | assumption
              | rfl
              | (simp only [M6.EuclidStorage.slotsFit, hz] at ⊢
                 dsimp only
                 repeat' apply And.intro
                 all_goals omega))
          | (simp only [M6.EuclidStorage.slotsFit, hz] at ⊢
             dsimp only
             repeat' apply And.intro
             all_goals omega)
