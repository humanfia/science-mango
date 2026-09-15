import M6Flatten
import Mathlib.LinearAlgebra.Prod
open scoped BigOperators
namespace M6.Spaces
noncomputable def convLinear (N : ℕ) [NeZero N] (a : M6.Physical.Block N) :
    M6.Physical.Block N →ₗ[ZMod 2] M6.Physical.Block N where
  toFun := M6.Physical.conv N a
  map_add' := M6.Physical.conv_add N a
  map_smul' := by
    intro c h
    funext i
    simp only [M6.Physical.conv, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
noncomputable def boundaryLinear (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) :
    M6.Physical.Block N →ₗ[ZMod 2] M6.Physical.Word N :=
  (convLinear N a).prod (convLinear N b)
noncomputable def flattenLinear (N : ℕ) :
    M6.Physical.Word N →ₗ[ZMod 2] M6.Pinned.Vector (2*N) where
  toFun := M6.Flatten.flatten N
  map_add' := by
    intro z w
    funext i
    by_cases hi : i.val < N <;> simp [M6.Flatten.flatten, hi]
  map_smul' := by
    intro c z
    funext i
    by_cases hi : i.val < N <;> simp [M6.Flatten.flatten, hi]
noncomputable def JLinear (N : ℕ) : M6.Physical.Word N →ₗ[ZMod 2] M6.Physical.Word N where
  toFun := M6.Physical.J N
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
noncomputable def boundary (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) :=
  (flattenLinear N).comp (boundaryLinear N a b)
noncomputable def dualBoundary (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) :=
  (flattenLinear N).comp ((JLinear N).comp (boundaryLinear N a b))
noncomputable def B (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) := (boundary N a b).range
noncomputable def D (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) := (dualBoundary N a b).range
noncomputable def boundaryWords (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) := M6.Character.subspaceWords (B N a b)
noncomputable def cycleWords (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) := M6.Character.dualWords (D N a b)
noncomputable def logicalWords (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) : Finset (M6.Pinned.Vector (2*N)) := by
  classical
  exact cycleWords N a b \ boundaryWords N a b
end M6.Spaces
