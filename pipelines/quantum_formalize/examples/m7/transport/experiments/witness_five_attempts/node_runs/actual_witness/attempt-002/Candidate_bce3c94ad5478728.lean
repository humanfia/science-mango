import FrozenTarget_bce3c94ad5478728
theorem M7.Transport.actual_witness : QuantumHarnessFrozenTarget := by
  intro N w inst g c d k v hA hB h0A h0B hg hs
  classical
  have ha := M7.Domain.admissible N w c.1 c.2 hA hB h0A h0B hg
  have hc := M6.Final.answer_correct N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ha
  simp only [M6.Final.AnswerCorrect, M6.Final.LX, M7.Domain.coefficients_indicator] at hc
  have hb : M7.Transport.distance c = some d ∧
      v ∈ M7.Transport.LX c ∧ M6.Pinned.weight v = d ∧ k ≤ 2*N := by
    simp only [M7.Transport.distance, M7.Transport.LX, M7.Transport.BX,
      M7.Transport.CX, M7.Domain.coefficients_indicator]
    aesop
  rcases hb with ⟨hd, hv, hw, hk⟩
  have hx := (M7.Transport.x_logical N g c v).mpr hv
  have hwx : M6.Pinned.weight (M7.Transport.Xmap g v) = d :=
    ((M7.Transport.action_isometry N g c).2 v).2.2.trans hw
  refine ⟨(M7.Transport.distance_invariant N g c).trans hd, hx, hwx, ?_, ?_, hk⟩
  · exact (M6.ActualCSS.J_logical_iff N
      (M7.Supports.indicator (M7.Action.act g c).1)
      (M7.Supports.indicator (M7.Action.act g c).2)
      (M7.Transport.Xmap g v)).mp hx
  · exact (M6.Flatten.J_weight N (M7.Transport.Xmap g v)).trans hwx
