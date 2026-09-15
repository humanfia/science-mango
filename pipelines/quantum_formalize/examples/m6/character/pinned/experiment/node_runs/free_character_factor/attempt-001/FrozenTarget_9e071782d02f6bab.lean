import M6CharacterAccepted
import M6PinnedCharacter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (i : Fin m) (s : ZMod 2), M6.Character.pinnedCharacterFactor (M6.Pinned.free m) i s = 1 + Polynomial.C (M6.Character.sign s) * Polynomial.X
