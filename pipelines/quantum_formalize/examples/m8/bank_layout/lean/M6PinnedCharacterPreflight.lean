import M6CharacterAccepted
import M6PinnedCharacter
open scoped BigOperators
def target_0 : Prop := ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
#check target_0
def target_1 : Prop := ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Character.Vector m), (∏ i, M6.Character.boundaryFactor P i (v i)) = M6.Character.pinnedMonomial P v
#check target_1
def target_2 : Prop := ∀ (m : ℕ) (i : Fin m) (s : ZMod 2), M6.Character.pinnedCharacterFactor (M6.Pinned.free m) i s = 1 + Polynomial.C (M6.Character.sign s) * Polynomial.X
#check target_2
def target_3 : Prop := ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (P : M6.Pinned.Pins m), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Pinned.enumerator (M6.Character.dualWords D) P = M6.Character.pinnedTransform D P
#check target_3
