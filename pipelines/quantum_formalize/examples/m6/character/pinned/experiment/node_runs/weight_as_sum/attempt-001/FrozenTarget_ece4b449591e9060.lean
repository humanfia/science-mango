import M6CharacterAccepted
import M6PinnedCharacter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
