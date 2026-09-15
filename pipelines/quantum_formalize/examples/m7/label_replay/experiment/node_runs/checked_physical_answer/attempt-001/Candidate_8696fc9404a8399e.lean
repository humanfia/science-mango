import FrozenTarget_8696fc9404a8399e
theorem M7.LabelReplay.checked_physical_answer : QuantumHarnessFrozenTarget := by
  intro N w inst c r hA hB h0A h0B hconn hcheck
  have hs := (M7.LabelReplay.check_sound N c r hcheck).2.2.1
  have hp := M7.ClosedSolve.closed_pointwise N w c hA hB h0A h0B hconn
  have ha := hp.2.2.1
  rw [hs]
  constructor
  · exact ha.1
  · intro d k v hv
    have hw := ha.2.2.1
    first
    | specialize hw d k v hv
    | specialize hw d v k hv
    simpa only [M7.DefaultQuery.distance, M7.Transport.distance,
      M6.Final.LX, M6.Final.CX, M6.Final.BX, M6.Final.CZ, M6.Final.BZ,
      M7.Transport.LX, M7.Transport.CX, M7.Transport.BX,
      M7.Transport.LZ, M7.Transport.CZ, M7.Transport.BZ,
      M7.Domain.coefficients_indicator] using hw
