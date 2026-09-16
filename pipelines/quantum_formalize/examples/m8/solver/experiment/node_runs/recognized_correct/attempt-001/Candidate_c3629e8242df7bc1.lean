import FrozenTarget_c3629e8242df7bc1
theorem M8.Solver.recognized_correct : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c w hw hvalid F d z choice k hrun
  simp only [M8.Solver.run, M8.Solver.originalF_signature N c] at hrun
  split at hrun
  · cases hrun
  · rename_i hF
    cases hdiscover : M8.Discovery.discover c with
    | none =>
        simp [hdiscover] at hrun
    | some chosen =>
        have hanchor : M8.PhysicalBridge.Anchored
            (M7.Action.act (M8.Discovery.action chosen) c) :=
          M8.Discovery.anchored N c chosen hdiscover
        obtain ⟨d', v, k', hsolve, hdist, hmem, hweight, hmin, hbound⟩ :=
          M8.PhysicalBridge.minimum_original_witness N c
            (M8.Discovery.action chosen) w hvalid hanchor hF
        have hsolve' : M8.PhysicalBridge.solve (M8.Discovery.transformed c chosen) =
            some (d', v, k') := hsolve
        simp only [hdiscover, hsolve'] at hrun
        injection hrun with hFeq hdeq hzeq hchoiceeq hkeq
        subst F
        subst d
        subst z
        subst choice
        subst k
        exact ⟨rfl, hdiscover, hdist, hmem, hweight, hmin, hbound,
          M8.Discovery.lex_first N c chosen hdiscover,
          M8.RawParameters.encoded_dimension N w c hw hvalid⟩
