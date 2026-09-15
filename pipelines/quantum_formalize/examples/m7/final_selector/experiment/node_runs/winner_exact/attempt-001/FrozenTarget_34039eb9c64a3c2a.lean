import M7FinalSelector

theorem M7.FinalSelector.index_feasible : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ x : M7.FinalSelector.Index N w q, M7.GlobalQuery.feasible q (M7.FinalSelector.family N w q) x ↔ M7.FinalSelector.RawFeasible w q (M7.FinalSelector.realize q x) := by
  intro N w inst q hw hwN hq x
  have hb : M7.PrefixOrbit.ClassValid w (M7.FinalSelector.family N w q x.1) :=
    (M7.GeneratedFamily.family_good N w (M7.QuerySectors.effective N q) hw hwN
      (M7.QuerySectors.effective_valid N q hq) x.1).1
  have hc : M7.PrefixOrbit.ClassValid w
      (M7.Action.act x.2 (M7.FinalSelector.family N w q x.1)) := by
    first
    | simpa only [M7.PrefixOrbit.class_action] using hb
    | solve_by_elim [M7.PrefixOrbit.class_action]
  simp only [M7.GlobalQuery.feasible, M7.FinalSelector.RawFeasible,
    M7.FinalSelector.realize, M7.GlobalQuery.realize,
    M7.DefaultQuery.feasible, M7.Action.act_identity,
    M7.QueryRebase.sector_base, hc, true_and, and_true]

theorem M7.FinalSelector.raw_realizable : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c → ∃ x : M7.FinalSelector.Index N w q, M7.FinalSelector.realize q x = c := by
  intro N w inst q hw hwN hq c hc
  have hv : M7.PrefixOrbit.ClassValid w c := hc.1
  have hs : M7.DefaultQuery.sectorTest q c c := by
    unfold M7.FinalSelector.RawFeasible M7.DefaultQuery.feasible at hc
    tauto
  have hall : ∀ d : M7.Action.Recipe N,
      M7.DefaultQuery.allows q (M7.DefaultQuery.signature d) →
        M7.RecipeSignature.signature d ∈ M7.QuerySectors.effective N q := by
    intro d hd
    exact (M7.QuerySectors.signature_allowed N q d).mpr hd
  have horbit : ∃ g : M7.Action.Record N,
      M7.RecipeSignature.signature (M7.Action.act g c) ∈ M7.QuerySectors.effective N q := by
    unfold M7.DefaultQuery.sectorTest at hs
    split at hs
    all_goals
      first
      | obtain ⟨g, hg⟩ := hs
        exact ⟨g, hall _ hg⟩
      | refine ⟨M7.Action.identity N, ?_⟩
        rw [M7.Action.act_identity]
        exact hall c hs
  obtain ⟨i, g, hg⟩ :=
    (M7.GeneratedFamily.family_complete N w (M7.QuerySectors.effective N q)
      hw hwN (M7.QuerySectors.effective_valid N q hq) c).mpr ⟨hv, horbit⟩
  exact ⟨(i, g), hg⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = true ↔ M7.FinalSelector.RawWinner w q (M7.FinalSelector.realize q x)
