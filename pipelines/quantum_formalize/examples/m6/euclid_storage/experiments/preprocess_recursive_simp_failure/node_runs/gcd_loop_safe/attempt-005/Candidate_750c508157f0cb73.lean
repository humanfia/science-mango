import FrozenTarget_750c508157f0cb73
theorem M6.EuclidStorage.gcd_loop_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  have hp (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).1
  have hq' (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.1
  have hsaved (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.2.1
  have hwork (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.1
  have hcancel (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.2.1
  have hpasses (n : ℕ) (u : M6.EuclidStorage.Slots) (a b : ℕ) :=
    (M6.EuclidStorage.rem_loop_refines n u a b).2.2.2.2.2.2
  have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
    simp [M6.Euclid.rank]
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
      · have hb := M6.Euclid.remainder_aux_correct
          (M6.Euclid.rank s.p) s.p s.q (le_refl _)
        have ht' := M6.Euclid.remainder_passes
          (M6.Euclid.rank s.p) s.p s.q
        have hd := (M6.Euclid.remainder_correct s.p s.q).2.2 hq
        simp only [M6.Euclid.remainder] at hd
        simp [M6.Euclid.euclidAux, hq, M6.Euclid.remainder] at hc he ht
        simp only [M6.EuclidStorage.gcdSafe, hq, ite_false]
        simp only [M6.EuclidStorage.slotsFit, hp, hq', hsaved,
          hwork, hcancel, hpasses, M6.Euclid.remainder,
          Nat.zero_add, Nat.add_zero, hz] at hs ⊢
        repeat' first
          | assumption
          | apply And.intro
          | apply ih
          | apply M6.EuclidStorage.rem_loop_safe
        all_goals
          simp only [M6.EuclidStorage.slotsFit, hp, hq', hsaved,
            hwork, hcancel, hpasses, M6.Euclid.remainder,
            Nat.zero_add, Nat.add_zero, hz] at *
        all_goals omega
