import M7ActualPresentationAccepted
import M7DefaultQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N), (q.sectorMode = M7.DefaultQuery.SectorMode.classSector → (M7.DefaultQuery.sectorTest q base placed ↔ ∃ g : M7.Action.Record N, M7.DefaultQuery.allows q (M7.DefaultQuery.signature (M7.Action.act g base)))) ∧ (q.sectorMode = M7.DefaultQuery.SectorMode.placementSector → (M7.DefaultQuery.sectorTest q base placed ↔ M7.DefaultQuery.allows q (M7.DefaultQuery.signature placed)))
