import FrozenTarget_595ceec5265177ed
theorem M8.Anchor.record_injective : QuantumHarnessFrozenTarget := by
  intro N _ e u a b a1 b1 h
  have ha := congrArg M7.Action.Record.leftShift h
  have hb := congrArg M7.Action.Record.rightShift h
  change -((u : ZMod N) * a) = -((u : ZMod N) * a1) at ha
  change -((u : ZMod N) * b) = -((u : ZMod N) * b1) at hb
  constructor
  · have h' := congrArg (fun x : ZMod N => (↑(u⁻¹) : ZMod N) * (-x)) ha
    simpa [← mul_assoc] using h'
  · have h' := congrArg (fun x : ZMod N => (↑(u⁻¹) : ZMod N) * (-x)) hb
    simpa [← mul_assoc] using h'
