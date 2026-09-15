import M6CharacterAccepted
import M6PinnedCharacter

theorem M6.Character.free_character_factor : ∀ (m : ℕ) (i : Fin m) (s : ZMod 2), M6.Character.pinnedCharacterFactor (M6.Pinned.free m) i s = 1 + Polynomial.C (M6.Character.sign s) * Polynomial.X := by
  change ∀ (m : ℕ) (i : Fin m) (s : ZMod 2), M6.Character.pinnedCharacterFactor (M6.Pinned.free m) i s = 1 + Polynomial.C (M6.Character.sign s) * Polynomial.X
  intro m i s
  classical
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hv : (1 : ZMod 2).val = 1 := rfl
  simp [M6.Character.pinnedCharacterFactor, M6.Character.boundaryFactor,
    M6.Pinned.free, h, M6.Character.sign, hv]
#print axioms M6.Character.free_character_factor
