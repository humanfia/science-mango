import M7ActualPresentation
import M7PresentationAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (g h : M7.Action.Record N), (M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h ↔ (g.unit : ZMod N).val < (h.unit : ZMod N).val ∨ (g.unit : ZMod N).val = (h.unit : ZMod N).val ∧ (g.exchange < h.exchange ∨ g.exchange = h.exchange ∧ (g.leftShift.val < h.leftShift.val ∨ g.leftShift.val = h.leftShift.val ∧ g.rightShift.val ≤ h.rightShift.val)))
