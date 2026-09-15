import M6CharacterAccepted
import M6Normalization


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = M6.FiberSum.fiberSum L w
