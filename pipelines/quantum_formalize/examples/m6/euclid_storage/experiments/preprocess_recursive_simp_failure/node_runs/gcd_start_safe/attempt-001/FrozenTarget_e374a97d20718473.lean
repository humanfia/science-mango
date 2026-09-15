import M6EuclidAccepted
import M6EuclidStorage

theorem M6.EuclidStorage.rem_loop_refines : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t : ℕ), let r := M6.EuclidStorage.remLoop fuel s c t; r.slots.p = s.p ∧ r.slots.q = s.q ∧ r.slots.saved = s.saved ∧ r.slots.work = (M6.Euclid.remainderAux fuel s.work s.q).value ∧ r.cancellations = c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ∧ r.rounds = 0 ∧ r.passes = t + (M6.Euclid.remainderAux fuel s.work s.q).passes := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t : ℕ), let r := M6.EuclidStorage.remLoop fuel s c t; r.slots.p = s.p ∧ r.slots.q = s.q ∧ r.slots.saved = s.saved ∧ r.slots.work = (M6.Euclid.remainderAux fuel s.work s.q).value ∧ r.cancellations = c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ∧ r.rounds = 0 ∧ r.passes = t + (M6.Euclid.remainderAux fuel s.work s.q).passes
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t
      simp [M6.EuclidStorage.remLoop, M6.Euclid.remainderAux]
  | succ fuel ih =>
      intro s c t
      simp only [M6.EuclidStorage.remLoop, M6.Euclid.remainderAux]
      split <;> simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem M6.EuclidStorage.rem_loop_safe : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ≤ 32*width → t + (M6.Euclid.remainderAux fuel s.work s.q).passes ≤ 32*width → M6.EuclidStorage.remSafe fuel s c t width := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ≤ 32*width → t + (M6.Euclid.remainderAux fuel s.work s.q).passes ≤ 32*width → M6.EuclidStorage.remSafe fuel s c t width
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c t width hwidth hs hf hc ht
      simp [M6.Euclid.remainderAux] at hc ht
      simp [M6.EuclidStorage.remSafe]
      simp only [M6.EuclidStorage.slotsFit] at hs ⊢
      repeat' constructor <;> omega
  | succ fuel ih =>
      intro s c t width hwidth hs hf hc ht
      by_cases hw : s.work = 0
      · simp [M6.Euclid.remainderAux, hw] at hc ht
        simp [M6.EuclidStorage.remSafe, hw]
        simp only [M6.EuclidStorage.slotsFit] at hs ⊢
        repeat' constructor <;> omega
      · by_cases hq : s.q = 0
        · simp [M6.Euclid.remainderAux, hw, hq] at hc ht
          simp [M6.EuclidStorage.remSafe, hw, hq]
          simp only [M6.EuclidStorage.slotsFit] at hs ⊢
          repeat' constructor <;> omega
        · by_cases hd : s.work.degree < s.q.degree
          · simp [M6.Euclid.remainderAux, hw, hq, hd] at hc ht
            simp [M6.EuclidStorage.remSafe, hw, hq, hd]
            simp only [M6.EuclidStorage.slotsFit] at hs ⊢
            repeat' constructor <;> omega
          · have hle : s.q.degree ≤ s.work.degree := le_of_not_gt hd
            have hdrop := M6.Euclid.cancel_drop s.work s.q hw hq hle
            have hs' : M6.EuclidStorage.slotsFit width
                { s with work := M6.Euclid.cancel s.work s.q } := by
              simp only [M6.EuclidStorage.slotsFit] at hs ⊢
              repeat' constructor <;> omega
            simp [M6.Euclid.remainderAux, hw, hq, hd] at hc ht
            have hrec := ih { s with work := M6.Euclid.cancel s.work s.q }
              (c + 1) (t + 2) width hwidth hs' (by omega)
              (by dsimp; omega) (by dsimp; omega)
            simp only [M6.EuclidStorage.remSafe]
            simp only [hw, hq, hd, ite_true, ite_false, false_or, or_false,
              false_and, and_false, true_and, and_true, not_false_eq_true]
            simp only [M6.EuclidStorage.slotsFit] at hs ⊢
            repeat' first | assumption | apply And.intro | omega

theorem M6.EuclidStorage.gcd_loop_safe : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → s.work = 0 → fuel ≤ 32*width → c + (M6.Euclid.euclidAux fuel s.p s.q).cancellations ≤ 32*width → e + (M6.Euclid.euclidAux fuel s.p s.q).rounds ≤ 32*width → t + (M6.Euclid.euclidAux fuel s.p s.q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe fuel s c e t width := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → s.work = 0 → fuel ≤ 32*width → c + (M6.Euclid.euclidAux fuel s.p s.q).cancellations ≤ 32*width → e + (M6.Euclid.euclidAux fuel s.p s.q).rounds ≤ 32*width → t + (M6.Euclid.euclidAux fuel s.p s.q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe fuel s c e t width
  )
  change QuantumHarnessFrozenTarget
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (p q saved : M6.Euclid.BP) (c e t width : ℕ), 0 < width → M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.rank saved ≤ width → c + (M6.Euclid.euclid p q).cancellations ≤ 32*width → e + (M6.Euclid.euclid p q).rounds ≤ 32*width → t + (M6.Euclid.euclid p q).passes ≤ 32*width → M6.EuclidStorage.gcdSafe (M6.Euclid.rank q+1) ⟨p,q,0,saved⟩ c e (t+1) width
