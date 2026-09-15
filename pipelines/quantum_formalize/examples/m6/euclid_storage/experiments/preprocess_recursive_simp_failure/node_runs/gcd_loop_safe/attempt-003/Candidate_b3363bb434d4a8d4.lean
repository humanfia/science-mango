import FrozenTarget_b3363bb434d4a8d4
theorem M6.EuclidStorage.gcd_loop_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c e t width hwidth hs hw hf hc he ht
      simp only [M6.Euclid.euclidAux] at hc he ht
      simp only [M6.EuclidStorage.gcdSafe]
      simp only [M6.EuclidStorage.slotsFit] at hs ⊢
      repeat' constructor <;> omega
  | succ fuel ih =>
      intro s c e t width hwidth hs hw hf hc he ht
      by_cases hq : s.q = 0
      · simp [M6.Euclid.euclidAux, hq] at hc he ht
        simp [M6.EuclidStorage.gcdSafe, hq]
        simp only [M6.EuclidStorage.slotsFit] at hs ⊢
        repeat' constructor <;> omega
      · have hr := M6.Euclid.remainder_correct s.p s.q
        have ha := M6.Euclid.remainder_aux_correct
          (M6.Euclid.rank s.p) s.p s.q (le_refl _)
        have htrem := M6.Euclid.remainder_passes
          (M6.Euclid.rank s.p) s.p s.q
        simp only [M6.Euclid.remainder] at hr
        have hp' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
          (M6.EuclidStorage.rem_loop_refines n u a b).1
        have hq' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
          (M6.EuclidStorage.rem_loop_refines n u a b).2.1
        have hs' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
          (M6.EuclidStorage.rem_loop_refines n u a b).2.2.1
        have hw' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
          (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.1
        have hc' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
          (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.2.1
        have he' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
          (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.2.2.1
        have ht' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
          (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.2.2.2
        simp only [M6.Euclid.euclidAux, hq, if_false,
          M6.Euclid.remainder] at hc he ht
        simp only [M6.EuclidStorage.gcdSafe, hq, if_false]
        simp only [hp', hq', hs', hw', hc', he', ht']
        dsimp only at hc he ht ⊢
        repeat' first
          | assumption
          | apply And.intro
          | apply ih
          | apply M6.EuclidStorage.rem_loop_safe
        all_goals
          simp only [M6.EuclidStorage.slotsFit] at hs ⊢
          simp only [hp', hq', hs', hw', hc', he', ht',
            M6.Euclid.remainder] at *
          dsimp only at *
          simp only [M6.Euclid.rank, if_pos rfl] at *
          repeat' constructor <;> omega
