import M6EuclidAccepted
import M6EuclidStorage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (s u : M6.EuclidStorage.Slots), M6.EuclidStorage.slotsFit (N+1) s → M6.EuclidStorage.slotsFit (N+1) u → M6.Euclid.dense N s.p = M6.Euclid.dense N u.p → M6.Euclid.dense N s.q = M6.Euclid.dense N u.q → M6.Euclid.dense N s.work = M6.Euclid.dense N u.work → M6.Euclid.dense N s.saved = M6.Euclid.dense N u.saved → s = u
