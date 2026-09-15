import M7QualityTable

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → ∀ g : M7.Action.Record N, (M7.DefaultQuery.dimension (M7.Action.act g c), M7.DefaultQuery.distance (M7.Action.act g c)) = M7.QualityTable.cache c
