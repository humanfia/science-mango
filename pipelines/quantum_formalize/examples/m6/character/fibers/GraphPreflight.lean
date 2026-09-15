import M6CharacterAccepted
import M6Normalization
open scoped BigOperators
def target_0 : Prop := ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = M6.FiberSum.fiberSum L w
#check target_0
def target_1 : Prop := ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → ∀ (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = Polynomial.C (k : ℤ) * ∑ b, w b
#check target_1
def target_2 : Prop := ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → Fintype.card α = k * Fintype.card β
#check target_2
def target_3 : Prop := ∀ (m : ℕ) (q : M6.Character.Vector m), (q = 0 → M6.Character.localTransform (fun _ _ => (1 : Polynomial ℤ)) q = Polynomial.C ((2 : ℤ)^m)) ∧ (q ≠ 0 → M6.Character.localTransform (fun _ _ => (1 : Polynomial ℤ)) q = 0)
#check target_3
def target_4 : Prop := ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)), (M6.Character.subspaceWords D).card * (M6.Character.dualWords D).card = 2^m
#check target_4
