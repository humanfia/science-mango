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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t width : ℕ), 0 < width → M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ≤ 32*width → t + (M6.Euclid.remainderAux fuel s.work s.q).passes ≤ 32*width → M6.EuclidStorage.remSafe fuel s c t width
