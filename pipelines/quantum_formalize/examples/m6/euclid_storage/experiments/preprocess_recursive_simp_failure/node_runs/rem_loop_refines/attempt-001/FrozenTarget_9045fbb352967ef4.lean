import M6EuclidAccepted
import M6EuclidStorage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (fuel : ℕ) (s : M6.EuclidStorage.Slots) (c t : ℕ), let r := M6.EuclidStorage.remLoop fuel s c t; r.slots.p = s.p ∧ r.slots.q = s.q ∧ r.slots.saved = s.saved ∧ r.slots.work = (M6.Euclid.remainderAux fuel s.work s.q).value ∧ r.cancellations = c + (M6.Euclid.remainderAux fuel s.work s.q).cancellations ∧ r.rounds = 0 ∧ r.passes = t + (M6.Euclid.remainderAux fuel s.work s.q).passes
