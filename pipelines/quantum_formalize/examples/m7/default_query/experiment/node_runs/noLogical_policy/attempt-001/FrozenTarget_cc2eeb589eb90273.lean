import M7ActualPresentationAccepted
import M7DefaultQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N), (M7.DefaultQuery.needsDistance q → M7.DefaultQuery.distance placed = none → ¬ M7.DefaultQuery.feasible q base placed) ∧ (q.distanceFloor = none → M7.DefaultQuery.Coordinate.negativeDistance ∉ q.objectives → (M7.DefaultQuery.feasible q base placed ↔ M7.DefaultQuery.valid N q ∧ M7.DefaultQuery.dimension placed ∈ q.dimensions ∧ M7.DefaultQuery.sectorTest q base placed ∧ (match q.localityCap with | none => True | some cap => M7.DefaultQuery.locality placed ≤ cap) ∧ (match q.radiusCap with | none => True | some cap => M7.DefaultQuery.radius placed ≤ cap)))
