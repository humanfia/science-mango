import FrozenTarget_81677128fa115204
theorem M8.RawParameters.raw_noLogical : QuantumHarnessFrozenTarget := by
  intro N w inst c hw hv
  classical
  obtain ⟨g, hg⟩ := M8.RawParameters.raw_anchor N w c hw hv
  have hp := M8.PhysicalBridge.pointwise_optimizer N c g w hv hg
  have hn := M8.PhysicalBridge.noLogical N c g w hv hg
  have hi := M7.Transport.distance_invariant N g c
  have hsolve : M8.PhysicalBridge.solve (M7.Action.act g c) = none ↔ M7.Transport.distance (M7.Action.act g c) = none := by
    simp only [M6.Final.PointwiseCorrect, M6.Final.AnswerCorrect] at hp
    unfold M8.PhysicalBridge.solve M7.Transport.distance
    cases hs : M6.ActualTransfer.solve N (M7.Supports.polynomial (M7.Action.act g c).1) (M7.Supports.polynomial (M7.Action.act g c).2) with
    | none => aesop
    | some ans =>
      rcases ans with ⟨d, v, k⟩
      aesop
  have hd : M7.Transport.distance c = none ↔ M8.PhysicalBridge.signature c = 1 := by
    rw [← hi]
    exact hsolve.symm.trans hn
  refine ⟨hd, ?_⟩
  apply Iff.trans _ hd
  have hc := M6.ActualCSS.common_quantum_distance N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2)
  simp only [M7.Transport.distance, M6.Final.quantumDistance, M6.Final.BX, M6.Final.CX, M6.Final.BZ, M6.Final.CZ, M7.Domain.coefficients_indicator, M7.Transport.LX, M7.Transport.BX, M7.Transport.CX] at hc ⊢
  first
  | have hs := M6.Pinned.distance_spec (M7.Transport.BX c) (M7.Transport.CX c)
    simp only [M7.Transport.BX, M7.Transport.CX] at hs
    aesop
  | have hs := M6.Pinned.distance_spec (2 * N) (M7.Transport.BX c) (M7.Transport.CX c)
    simp only [M7.Transport.BX, M7.Transport.CX] at hs
    aesop
