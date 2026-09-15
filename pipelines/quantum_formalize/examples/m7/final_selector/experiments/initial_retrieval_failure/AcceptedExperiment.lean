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

theorem M7.FinalSelector.invalid_rejection : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), (¬ M7.DefaultQuery.valid N q) → (∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.answer q x = Except.error M7.DefaultQuery.QueryError.invalidSignature) ∧ (¬ ∃ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c) := by
  intro N w inst q h
  constructor
  · intro x
    simp [M7.FinalSelector.answer, h]
  · simp [M7.FinalSelector.RawFeasible, M7.DefaultQuery.feasible, h]

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

theorem M7.FinalSelector.empty_exact : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ((∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = false) ↔ ¬ ∃ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c) := by
  intro N w inst q hw hwN hq
  classical
  have hbridge : (∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = false) ↔ M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) = ∅ := by
    constructor
    · intro h
      apply Finset.ext
      intro x
      constructor
      · intro hx
        have ht := (M7.StreamingIndices.stream_winners _ N q (M7.FinalSelector.family N w q) x).mpr hx
        change M7.FinalSelector.win q x = true at ht
        rw [h x] at ht
        cases ht
      · intro hx
        simpa using hx
    · intro he x
      cases hx : M7.FinalSelector.win q x with
      | false => rfl
      | true =>
        have ht : M7.StreamingIndices.streamWin q (M7.FinalSelector.family N w q) x = true := hx
        have hm := (M7.StreamingIndices.stream_winners _ N q (M7.FinalSelector.family N w q) x).mp ht
        rw [he] at hm
        simpa using hm
  rw [hbridge, (M7.GlobalQuery.winners_exact _ N q (M7.FinalSelector.family N w q)).2]
  constructor
  · intro h ⟨c, hc⟩
    obtain ⟨x, hx⟩ := M7.FinalSelector.raw_realizable N w q hw hwN hq c hc
    apply h
    refine ⟨x, (M7.FinalSelector.index_feasible N w q hw hwN hq x).mpr ?_⟩
    rw [hx]
    exact hc
  · intro h ⟨x, hx⟩
    exact h ⟨M7.FinalSelector.realize q x, (M7.FinalSelector.index_feasible N w q hw hwN hq x).mp hx⟩

theorem M7.FinalSelector.winner_exact : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = true ↔ M7.FinalSelector.RawWinner w q (M7.FinalSelector.realize q x) := by
  intro N w inst q hw hwN hq x
  rw [M7.FinalSelector.win, M7.StreamingIndices.stream_winners]
  rw [(M7.GlobalQuery.winners_exact _ N q (M7.FinalSelector.family N w q)).1 x]
  unfold M7.FinalSelector.RawWinner
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨(M7.FinalSelector.index_feasible N w q hw hwN hq x).mp hx, ?_⟩
    intro c hc
    obtain ⟨y, hy⟩ := M7.FinalSelector.raw_realizable N w q hw hwN hq c hc
    have hf := (M7.FinalSelector.index_feasible N w q hw hwN hq y).mpr (hy ▸ hc)
    have hm := hmin y hf
    rw [← hy]
    simpa only [M7.GlobalQuery.objective, M7.FinalSelector.realize,
      M7.GlobalQuery.realize, M7.Action.act_identity] using hm
  · rintro ⟨hx, hmin⟩
    refine ⟨(M7.FinalSelector.index_feasible N w q hw hwN hq x).mpr hx, ?_⟩
    intro y hy
    have hm := hmin (M7.FinalSelector.realize q y)
      ((M7.FinalSelector.index_feasible N w q hw hwN hq y).mp hy)
    simpa only [M7.GlobalQuery.objective, M7.FinalSelector.realize,
      M7.GlobalQuery.realize, M7.Action.act_identity] using hm

theorem M7.FinalSelector.raw_output : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ c : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q c ↔ ∃ x : M7.FinalSelector.Index N w q, M7.FinalSelector.win q x = true ∧ M7.FinalSelector.realize q x = c := by
  intro N w inst q hw hwN hq c
  constructor
  · intro hc
    obtain ⟨x, hx⟩ := M7.FinalSelector.raw_realizable N w q hw hwN hq c hc.1
    refine ⟨x, ?_, hx⟩
    apply (M7.FinalSelector.winner_exact N w q hw hwN hq x).mpr
    rw [hx]
    exact hc
  · rintro ⟨x, hx, hxc⟩
    have hc := (M7.FinalSelector.winner_exact N w q hw hwN hq x).mp hx
    rw [hxc] at hc
    exact hc

theorem M7.FinalSelector.strict_dominator : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c → ¬ M7.FinalSelector.RawWinner w q c → ∃ d : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q d ∧ M7.Selection.better q.order (M7.DefaultQuery.objective q d) (M7.DefaultQuery.objective q c) := by
  intro N w inst q hw hwN hq c hc hnot
  obtain ⟨x, hx⟩ := M7.FinalSelector.raw_realizable N w q hw hwN hq c hc
  have hbridge : ∀ y : M7.FinalSelector.Index N w q,
      y ∈ M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) ↔
        M7.FinalSelector.RawWinner w q (M7.FinalSelector.realize q y) := by
    intro y
    simpa only [M7.FinalSelector.win, M7.StreamingIndices.stream_winners] using
      (M7.FinalSelector.winner_exact N w q hw hwN hq y)
  have hf : M7.GlobalQuery.feasible q (M7.FinalSelector.family N w q) x :=
    (M7.FinalSelector.index_feasible N w q hw hwN hq x).mpr (hx ▸ hc)
  have hn : x ∉ M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) := by
    intro h
    apply hnot
    rw [← hx]
    exact (hbridge x).mp h
  obtain ⟨y, hy, hbetter⟩ :=
    M7.GlobalQuery.strict_dominator _ N q (M7.FinalSelector.family N w q) x hf hn
  refine ⟨M7.FinalSelector.realize q y, (hbridge y).mp hy, ?_⟩
  rw [← hx]
  simpa only [M7.GlobalQuery.objective, M7.FinalSelector.realize,
    M7.GlobalQuery.realize, M7.Action.act_identity] using hbetter
#print axioms M7.FinalSelector.index_feasible
#print axioms M7.FinalSelector.invalid_rejection
#print axioms M7.FinalSelector.raw_realizable
#print axioms M7.FinalSelector.empty_exact
#print axioms M7.FinalSelector.winner_exact
#print axioms M7.FinalSelector.raw_output
#print axioms M7.FinalSelector.strict_dominator
