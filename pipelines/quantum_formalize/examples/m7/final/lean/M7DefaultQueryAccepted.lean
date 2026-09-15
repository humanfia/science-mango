import M7ActualPresentationAccepted
import M7DefaultQuery
import M7SelectionAccepted

theorem M7.DefaultQuery.empty_objectives : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), q.objectives = [] → M7.DefaultQuery.winners q base = M7.Selection.feasibleSet Finset.univ (fun g : M7.Action.Record N => M7.DefaultQuery.feasible q base (M7.Action.act g base)) := by
  intro N inst q base h
  cases q
  dsimp only at h
  cases h
  unfold M7.DefaultQuery.winners
  change M7.Selection.select _ _ _ _ = _
  exact M7.Selection.empty_objectives _ _ _ _ _

theorem M7.DefaultQuery.literal_fiber : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N) (g h : M7.Action.Record N), M7.Action.act g base = M7.Action.act h base → ((M7.DefaultQuery.feasible q base (M7.Action.act g base) ↔ M7.DefaultQuery.feasible q base (M7.Action.act h base)) ∧ M7.DefaultQuery.objective q (M7.Action.act g base) = M7.DefaultQuery.objective q (M7.Action.act h base)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N) (g h : M7.Action.Record N), M7.Action.act g base = M7.Action.act h base → ((M7.DefaultQuery.feasible q base (M7.Action.act g base) ↔ M7.DefaultQuery.feasible q base (M7.Action.act h base)) ∧ M7.DefaultQuery.objective q (M7.Action.act g base) = M7.DefaultQuery.objective q (M7.Action.act h base))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst q base g h heq
  rw [heq]
  exact ⟨Iff.rfl, rfl⟩

theorem M7.DefaultQuery.noLogical_policy : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N), (M7.DefaultQuery.needsDistance q → M7.DefaultQuery.distance placed = none → ¬ M7.DefaultQuery.feasible q base placed) ∧ (q.distanceFloor = none → M7.DefaultQuery.Coordinate.negativeDistance ∉ q.objectives → (M7.DefaultQuery.feasible q base placed ↔ M7.DefaultQuery.valid N q ∧ M7.DefaultQuery.dimension placed ∈ q.dimensions ∧ M7.DefaultQuery.sectorTest q base placed ∧ (match q.localityCap with | none => True | some cap => M7.DefaultQuery.locality placed ≤ cap) ∧ (match q.radiusCap with | none => True | some cap => M7.DefaultQuery.radius placed ≤ cap))) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N), (M7.DefaultQuery.needsDistance q → M7.DefaultQuery.distance placed = none → ¬ M7.DefaultQuery.feasible q base placed) ∧ (q.distanceFloor = none → M7.DefaultQuery.Coordinate.negativeDistance ∉ q.objectives → (M7.DefaultQuery.feasible q base placed ↔ M7.DefaultQuery.valid N q ∧ M7.DefaultQuery.dimension placed ∈ q.dimensions ∧ M7.DefaultQuery.sectorTest q base placed ∧ (match q.localityCap with | none => True | some cap => M7.DefaultQuery.locality placed ≤ cap) ∧ (match q.radiusCap with | none => True | some cap => M7.DefaultQuery.radius placed ≤ cap)))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst q base placed
  constructor
  · intro hneed hdist hfeasible
    simp [M7.DefaultQuery.feasible, hneed, hdist] at hfeasible
  · intro hfloor hobjectives
    cases hlocality : q.localityCap <;>
      cases hradius : q.radiusCap <;>
      simp [M7.DefaultQuery.feasible, M7.DefaultQuery.needsDistance,
        M7.DefaultQuery.floorTest, hfloor, hobjectives, hlocality, hradius]

theorem M7.DefaultQuery.presentation_exact : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g ∈ M7.DefaultQuery.winners q base, ∃! h : M7.Action.Record N, M7.DefaultQuery.present q base h ∧ M7.Action.act h base = M7.Action.act g base ) ∧ (∀ g : M7.Action.Record N, M7.DefaultQuery.present q base g → g ∈ M7.DefaultQuery.winners q base ∧ ∀ h : M7.Action.Record N, M7.Action.act h base = M7.Action.act g base → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h) := by
  intro N inst q base
  constructor
  · intro g hg
    exact M7.ActualPresentation.presentation_exact N base q.objectives.length
      (M7.DefaultQuery.feasible q base) (M7.DefaultQuery.objective q) _ g hg
  · intro g hg
    exact M7.ActualPresentation.presentation_sound N base q.objectives.length
      (M7.DefaultQuery.feasible q base) (M7.DefaultQuery.objective q) _ g hg

theorem M7.DefaultQuery.sector_modes : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N), (q.sectorMode = M7.DefaultQuery.SectorMode.classSector → (M7.DefaultQuery.sectorTest q base placed ↔ ∃ g : M7.Action.Record N, M7.DefaultQuery.allows q (M7.DefaultQuery.signature (M7.Action.act g base)))) ∧ (q.sectorMode = M7.DefaultQuery.SectorMode.placementSector → (M7.DefaultQuery.sectorTest q base placed ↔ M7.DefaultQuery.allows q (M7.DefaultQuery.signature placed))) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N), (q.sectorMode = M7.DefaultQuery.SectorMode.classSector → (M7.DefaultQuery.sectorTest q base placed ↔ ∃ g : M7.Action.Record N, M7.DefaultQuery.allows q (M7.DefaultQuery.signature (M7.Action.act g base)))) ∧ (q.sectorMode = M7.DefaultQuery.SectorMode.placementSector → (M7.DefaultQuery.sectorTest q base placed ↔ M7.DefaultQuery.allows q (M7.DefaultQuery.signature placed)))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst q base placed
  constructor
  · intro h
    simp [M7.DefaultQuery.sectorTest, h]
  · intro h
    simp [M7.DefaultQuery.sectorTest, h]

theorem M7.DefaultQuery.strict_dominator : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N) (g : M7.Action.Record N), M7.DefaultQuery.feasible q base (M7.Action.act g base) → g ∉ M7.DefaultQuery.winners q base → ∃ h ∈ M7.DefaultQuery.winners q base, M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N) (g : M7.Action.Record N), M7.DefaultQuery.feasible q base (M7.Action.act g base) → g ∉ M7.DefaultQuery.winners q base → ∃ h ∈ M7.DefaultQuery.winners q base, M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst q base g hg hnot
  classical
  exact M7.Selection.selector_strict_dominator
    (M7.Action.Record N) q.objectives.length Finset.univ
    (fun h => M7.DefaultQuery.feasible q base (M7.Action.act h base))
    (fun h => M7.DefaultQuery.objective q (M7.Action.act h base))
    q.order g (Finset.mem_univ g) hg hnot

theorem M7.DefaultQuery.winners_exact : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g : M7.Action.Record N, g ∈ M7.DefaultQuery.winners q base ↔ M7.DefaultQuery.feasible q base (M7.Action.act g base) ∧ ∀ h : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act h base) → ¬ M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base))) ∧ (M7.DefaultQuery.winners q base = ∅ ↔ ¬ ∃ g : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act g base)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g : M7.Action.Record N, g ∈ M7.DefaultQuery.winners q base ↔ M7.DefaultQuery.feasible q base (M7.Action.act g base) ∧ ∀ h : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act h base) → ¬ M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base))) ∧ (M7.DefaultQuery.winners q base = ∅ ↔ ¬ ∃ g : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act g base))
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro N inst q base
  simpa [M7.DefaultQuery.winners, M7.ActualPresentation.selected,
    M7.Selection.feasibleSet, Finset.filter_eq_empty_iff] using
    (M7.Selection.selector_exact (M7.Action.Record N) q.objectives.length
      (Finset.univ : Finset (M7.Action.Record N))
      (fun g => M7.DefaultQuery.feasible q base (M7.Action.act g base))
      (fun g => M7.DefaultQuery.objective q (M7.Action.act g base)) q.order)

theorem M7.DefaultQuery.invalid_rejection : ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (¬ M7.DefaultQuery.valid N q → M7.DefaultQuery.answer q base = Except.error M7.DefaultQuery.QueryError.invalidSignature ∧ M7.DefaultQuery.winners q base = ∅) ∧ (M7.DefaultQuery.valid N q → M7.DefaultQuery.answer q base = Except.ok (M7.DefaultQuery.winners q base)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (¬ M7.DefaultQuery.valid N q → M7.DefaultQuery.answer q base = Except.error M7.DefaultQuery.QueryError.invalidSignature ∧ M7.DefaultQuery.winners q base = ∅) ∧ (M7.DefaultQuery.valid N q → M7.DefaultQuery.answer q base = Except.ok (M7.DefaultQuery.winners q base))
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro N inst q base
  constructor
  · intro hInvalid
    constructor
    · simp [M7.DefaultQuery.answer, hInvalid]
    · apply (M7.DefaultQuery.winners_exact N q base).2.mpr
      rintro ⟨g, hg⟩
      exact hInvalid hg.1
  · intro hValid
    simp [M7.DefaultQuery.answer, hValid]
#print axioms M7.DefaultQuery.empty_objectives
#print axioms M7.DefaultQuery.literal_fiber
#print axioms M7.DefaultQuery.noLogical_policy
#print axioms M7.DefaultQuery.presentation_exact
#print axioms M7.DefaultQuery.sector_modes
#print axioms M7.DefaultQuery.strict_dominator
#print axioms M7.DefaultQuery.winners_exact
#print axioms M7.DefaultQuery.invalid_rejection
