import M7QualityTable

theorem M7.QualityTable.array_scores : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (g : M7.Action.Record N), (M7.QualityTable.leftTable c (g.unit,g.exchange)).size = N ∧ (M7.QualityTable.rightTable c (g.unit,g.exchange)).size = N ∧ M7.QualityTable.placedScores c g = (M7.DefaultQuery.locality (M7.Action.act g c), M7.DefaultQuery.radius (M7.Action.act g c)) := by
  intro N inst c g
  refine ⟨?_, ?_, ?_⟩
  · simp [M7.QualityTable.leftTable]
  · simp [M7.QualityTable.rightTable]
  · simp [M7.QualityTable.placedScores, M7.QualityTable.read,
      M7.QualityTable.leftTable, M7.QualityTable.rightTable,
      ZMod.val_lt, ZMod.natCast_zmod_val]
    constructor <;> rfl

theorem M7.QualityTable.solve_distance : ∀ (N w : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → M7.QualityTable.solveDistance c = M7.DefaultQuery.distance c := by
  intro N w inst c hA hB h0A h0B hc
  have h := M7.ClosedSolve.closed_pointwise N w c hA hB h0A h0B hc
  have ha := h.2.2.1
  rcases ha with ⟨hn, hq, hr⟩
  unfold M7.QualityTable.solveDistance M7.DefaultQuery.distance M7.Transport.distance
  cases hs : M6.ActualTransfer.solve N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) with
  | none =>
      have hf := hn.mp hs
      have hd := hq.mpr hf
      simpa only [hs, Option.map_none] using hd.symm
  | some result =>
      rcases result with ⟨d, v, k⟩
      simp only [hs, Option.map_some]
      symm
      aesop

theorem M7.QualityTable.cache_action : ∀ (N w : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → ∀ g : M7.Action.Record N, (M7.DefaultQuery.dimension (M7.Action.act g c), M7.DefaultQuery.distance (M7.Action.act g c)) = M7.QualityTable.cache c := by
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
#print axioms M7.QualityTable.array_scores
#print axioms M7.QualityTable.solve_distance
#print axioms M7.QualityTable.cache_action
