import M7ActionAccepted
import M7GlobalQueryAccepted
import M7QueryRebase


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base placed : M7.Action.Recipe N) (g : M7.Action.Record N), (M7.DefaultQuery.sectorTest q (M7.Action.act g base) placed ↔ M7.DefaultQuery.sectorTest q base placed)
