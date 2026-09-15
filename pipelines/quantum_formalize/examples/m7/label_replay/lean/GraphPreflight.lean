import M7DefaultQuery
import M7SelectionAccepted
import M7ActualPresentationAccepted

noncomputable def M7.DefaultQueryTarget.sector_modes : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N), (q.sectorMode = M7.DefaultQuery.SectorMode.classSector → (M7.DefaultQuery.sectorTest q base placed ↔ ∃ g : M7.Action.Record N, M7.DefaultQuery.allows q (M7.DefaultQuery.signature (M7.Action.act g base)))) ∧ (q.sectorMode = M7.DefaultQuery.SectorMode.placementSector → (M7.DefaultQuery.sectorTest q base placed ↔ M7.DefaultQuery.allows q (M7.DefaultQuery.signature placed)))

#check M7.DefaultQueryTarget.sector_modes

noncomputable def M7.DefaultQueryTarget.noLogical_policy : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N), (M7.DefaultQuery.needsDistance q → M7.DefaultQuery.distance placed = none → ¬ M7.DefaultQuery.feasible q base placed) ∧ (q.distanceFloor = none → M7.DefaultQuery.Coordinate.negativeDistance ∉ q.objectives → (M7.DefaultQuery.feasible q base placed ↔ M7.DefaultQuery.valid N q ∧ M7.DefaultQuery.dimension placed ∈ q.dimensions ∧ M7.DefaultQuery.sectorTest q base placed ∧ (match q.localityCap with | none => True | some cap => M7.DefaultQuery.locality placed ≤ cap) ∧ (match q.radiusCap with | none => True | some cap => M7.DefaultQuery.radius placed ≤ cap)))

#check M7.DefaultQueryTarget.noLogical_policy

noncomputable def M7.DefaultQueryTarget.literal_fiber : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N) (g h : M7.Action.Record N), M7.Action.act g base = M7.Action.act h base → ((M7.DefaultQuery.feasible q base (M7.Action.act g base) ↔ M7.DefaultQuery.feasible q base (M7.Action.act h base)) ∧ M7.DefaultQuery.objective q (M7.Action.act g base) = M7.DefaultQuery.objective q (M7.Action.act h base))

#check M7.DefaultQueryTarget.literal_fiber

noncomputable def M7.DefaultQueryTarget.winners_exact : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g : M7.Action.Record N, g ∈ M7.DefaultQuery.winners q base ↔ M7.DefaultQuery.feasible q base (M7.Action.act g base) ∧ ∀ h : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act h base) → ¬ M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base))) ∧ (M7.DefaultQuery.winners q base = ∅ ↔ ¬ ∃ g : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act g base))

#check M7.DefaultQueryTarget.winners_exact

noncomputable def M7.DefaultQueryTarget.invalid_rejection : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (¬ M7.DefaultQuery.valid N q → M7.DefaultQuery.answer q base = Except.error M7.DefaultQuery.QueryError.invalidSignature ∧ M7.DefaultQuery.winners q base = ∅) ∧ (M7.DefaultQuery.valid N q → M7.DefaultQuery.answer q base = Except.ok (M7.DefaultQuery.winners q base))

#check M7.DefaultQueryTarget.invalid_rejection

noncomputable def M7.DefaultQueryTarget.strict_dominator : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N) (g : M7.Action.Record N), M7.DefaultQuery.feasible q base (M7.Action.act g base) → g ∉ M7.DefaultQuery.winners q base → ∃ h ∈ M7.DefaultQuery.winners q base, M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base))

#check M7.DefaultQueryTarget.strict_dominator

noncomputable def M7.DefaultQueryTarget.empty_objectives : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), q.objectives = [] → M7.DefaultQuery.winners q base = M7.Selection.feasibleSet Finset.univ (fun g : M7.Action.Record N => M7.DefaultQuery.feasible q base (M7.Action.act g base))

#check M7.DefaultQueryTarget.empty_objectives

noncomputable def M7.DefaultQueryTarget.presentation_exact : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g ∈ M7.DefaultQuery.winners q base, ∃! h : M7.Action.Record N, M7.DefaultQuery.present q base h ∧ M7.Action.act h base = M7.Action.act g base ) ∧ (∀ g : M7.Action.Record N, M7.DefaultQuery.present q base g → g ∈ M7.DefaultQuery.winners q base ∧ ∀ h : M7.Action.Record N, M7.Action.act h base = M7.Action.act g base → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h)

#check M7.DefaultQueryTarget.presentation_exact

