import FrozenTarget_a0004cbf23af687a
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
      · have hr := M6.Euclid.remainder_aux_correct
          (M6.Euclid.rank s.p) s.p s.q (le_refl _)
        have hpasses := M6.Euclid.remainder_passes
          (M6.Euclid.rank s.p) s.p s.q
        have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
          simp [M6.Euclid.rank]
        have rp := fun (n : ℕ) (v : M6.EuclidStorage.Slots) (a b : ℕ) =>
          (M6.EuclidStorage.rem_loop_refines n v a b).1
        have rq := fun (n : ℕ) (v : M6.EuclidStorage.Slots) (a b : ℕ) =>
          (M6.EuclidStorage.rem_loop_refines n v a b).2.1
        have rs := fun (n : ℕ) (v : M6.EuclidStorage.Slots) (a b : ℕ) =>
          (M6.EuclidStorage.rem_loop_refines n v a b).2.2.1
        have rwk := fun (n : ℕ) (v : M6.EuclidStorage.Slots) (a b : ℕ) =>
          (M6.EuclidStorage.rem_loop_refines n v a b).2.2.2.1
        have rc := fun (n : ℕ) (v : M6.EuclidStorage.Slots) (a b : ℕ) =>
          (M6.EuclidStorage.rem_loop_refines n v a b).2.2.2.2.1
        have re := fun (n : ℕ) (v : M6.EuclidStorage.Slots) (a b : ℕ) =>
          (M6.EuclidStorage.rem_loop_refines n v a b).2.2.2.2.2.1
        have rt := fun (n : ℕ) (v : M6.EuclidStorage.Slots) (a b : ℕ) =>
          (M6.EuclidStorage.rem_loop_refines n v a b).2.2.2.2.2.2
        simp only [M6.Euclid.euclidAux, hq, if_false,
          M6.Euclid.remainder] at hc he ht
        simp only [M6.EuclidStorage.slotsFit] at hs
        simp only [M6.EuclidStorage.gcdSafe, hq, if_false]
        simp only [rp, rq, rs, rwk, rc, re, rt, M6.Euclid.remainder]
        dsimp only
        repeat' first
          | assumption
          | apply And.intro
          | (apply M6.EuclidStorage.rem_loop_safe <;>
              first
              | assumption
              | (simp only [M6.EuclidStorage.slotsFit]; dsimp only; omega)
              | (dsimp only; omega))
          | (apply ih <;>
              first
              | assumption
              | rfl
              | (simp only [M6.EuclidStorage.slotsFit, hz]; dsimp only; omega)
              | (dsimp only; omega))
          | (simp only [M6.EuclidStorage.slotsFit, hz]; dsimp only; omega)
          | omega
