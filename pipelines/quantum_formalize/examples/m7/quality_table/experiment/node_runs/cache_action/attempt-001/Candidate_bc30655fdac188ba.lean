import FrozenTarget_bc30655fdac188ba
theorem M7.QualityTable.cache_action : QuantumHarnessFrozenTarget := by
  intro N w inst c hA hB h0A h0B hc g
  have hd : (M7.DefaultQuery.signature (M7.Action.act g c)).natDegree =
      (M7.DefaultQuery.signature c).natDegree :=
    M7.RecipeSignature.action_signature_degree N c g
  have hdim : M7.DefaultQuery.dimension (M7.Action.act g c) =
      M7.DefaultQuery.dimension c := by
    unfold M7.DefaultQuery.dimension
    rw [hd]
  have hdist : M7.DefaultQuery.distance (M7.Action.act g c) =
      M7.DefaultQuery.distance c :=
    M7.Transport.distance_invariant N g c
  change (M7.DefaultQuery.dimension (M7.Action.act g c),
      M7.DefaultQuery.distance (M7.Action.act g c)) =
    (M7.DefaultQuery.dimension c, M7.QualityTable.solveDistance c)
  rw [hdim, hdist, M7.QualityTable.solve_distance N w c hA hB h0A h0B hc]
