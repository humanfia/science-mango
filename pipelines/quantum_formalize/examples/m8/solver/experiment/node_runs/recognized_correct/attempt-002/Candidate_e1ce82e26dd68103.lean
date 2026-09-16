import FrozenTarget_e1ce82e26dd68103
theorem M8.Solver.recognized_correct : QuantumHarnessFrozenTarget := by
    classical
    intro N inst c w hw hvalid F d z choice k hrun
    by_cases hOne : M8.Solver.originalF c = 1
    · simp [M8.Solver.run, hOne] at hrun
    · simp only [M8.Solver.run, if_neg hOne] at hrun
      cases hdiscover : M8.Discovery.discover c with
      | none => simp [hdiscover] at hrun
      | some chosen =>
        have hsig : M8.PhysicalBridge.signature c ≠ 1 := by
          intro hs
          apply hOne
          rw [M8.Solver.originalF_signature N c]
          exact hs
        have hanchor := M8.Discovery.anchored N c chosen hdiscover
        obtain ⟨d', v, k', hsolve, hdist, hmem, hweight, hmin, hbound⟩ :=
          M8.PhysicalBridge.minimum_original_witness N c
            (M8.Discovery.action chosen) w hvalid hanchor hsig
        change M8.PhysicalBridge.solve (M8.Discovery.transformed c chosen) =
          some (d', v, k') at hsolve
        simp only [hdiscover, hsolve] at hrun
        injection hrun with hF hd hz hc hk
        subst F
        subst d
        subst z
        subst choice
        subst k
        refine ⟨M8.Solver.originalF_signature N c, ?_, hdist, hmem,
          hweight, hmin, hbound, ?_, ?_⟩
        · first | exact hdiscover | rfl
        · exact M8.Discovery.lex_first N c chosen hdiscover
        · simpa only [M8.Solver.originalF_signature N c] using
            M8.RawParameters.encoded_dimension N w c hw hvalid
