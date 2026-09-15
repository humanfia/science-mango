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

theorem M6.EuclidStorage.gcd_loop_refines : ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t : ℕ), s.work = 0 → let r := M6.EuclidStorage.gcdLoop fuel s c e t; r.slots.saved = s.saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclidAux fuel s.p s.q) c e t := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c e t : ℕ), s.work = 0 → let r := M6.EuclidStorage.gcdLoop fuel s c e t; r.slots.saved = s.saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclidAux fuel s.p s.q) c e t
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro fuel
  induction fuel with
  | zero =>
      intro s c e t hw
      simp [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
        M6.EuclidStorage.toRun, M6.EuclidStorage.offset, hw]
  | succ fuel ih =>
      intro s c e t hw
      by_cases hq : s.q = 0
      · simp [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
          M6.EuclidStorage.toRun, M6.EuclidStorage.offset, hq, hw]
      · have hr := fun (c t : ℕ) =>
          M6.EuclidStorage.rem_loop_refines (M6.Euclid.rank s.p)
            (⟨0, s.q, s.p, s.saved⟩ : M6.EuclidStorage.Slots) c t
        dsimp only at hr
        simp only [M6.EuclidStorage.gcdLoop, M6.Euclid.euclidAux,
          hq, if_false]
        simp only [M6.Euclid.remainder, hr, ih]
        simp [M6.EuclidStorage.offset, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (p q saved : M6.Euclid.BP) (c e t : ℕ), let r := M6.EuclidStorage.gcdStart p q saved c e t; r.slots.saved = saved ∧ r.slots.work = 0 ∧ M6.EuclidStorage.toRun r = M6.EuclidStorage.offset (M6.Euclid.euclid p q) c e t
