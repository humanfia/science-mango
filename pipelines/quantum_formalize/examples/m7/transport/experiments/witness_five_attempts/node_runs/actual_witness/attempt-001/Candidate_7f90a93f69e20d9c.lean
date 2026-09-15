import FrozenTarget_7f90a93f69e20d9c
theorem M7.Transport.actual_witness : QuantumHarnessFrozenTarget := by
  intro N w inst g c d k v hA hB h0A h0B hg hsolve
  classical
  have hadm := M7.Domain.admissible N w c.1 c.2 hA hB h0A h0B hg
  have hcorrect := M6.Final.answer_correct N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) hadm
  unfold M6.Final.AnswerCorrect at hcorrect
  have hbase : M7.Transport.distance c = some d ∧ v ∈ M7.Transport.LX c ∧ M6.Pinned.weight v = d ∧ k ≤ 2*N := by
    first
    | have hactual := hcorrect.2 d v k hsolve
    | have hactual := hcorrect.2.2 d v k hsolve
    | have hactual := hcorrect.1.2 d v k hsolve
    | have hactual := hcorrect.2.1 d v k hsolve
    | have hactual := hcorrect d v k hsolve
    | have hactual := hcorrect.2.2.2 d v k hsolve
    all_goals
      simp only [M6.Final.LX, M7.Domain.coefficients_indicator] at hactual
      simp only [M7.Transport.distance, M7.Transport.LX, M7.Domain.coefficients_indicator]
      aesop
  have hx : M7.Transport.Xmap g v ∈ M7.Transport.LX (M7.Action.act g c) :=
    (M7.Transport.x_logical N g c v).mpr hbase.2.1
  have hw : M6.Pinned.weight (M7.Transport.Xmap g v) = d :=
    ((M7.Transport.action_isometry N g c).2 v).2.2.trans hbase.2.2.1
  refine ⟨(M7.Transport.distance_invariant N g c).trans hbase.1, hx, hw, ?_, ?_, hbase.2.2.2⟩
  · exact (M6.ActualCSS.J_logical_iff N
      (M7.Supports.indicator (M7.Action.act g c).1)
      (M7.Supports.indicator (M7.Action.act g c).2)
      (M7.Transport.Xmap g v)).mp hx
  · exact (M6.Flatten.J_weight N (M7.Transport.Xmap g v)).trans hw
