import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
open scoped BigOperators
namespace M6.Physical
abbrev Block (N : ℕ) := ZMod N → ZMod 2
abbrev Word (N : ℕ) := Block N × Block N
noncomputable def conv (N : ℕ) [NeZero N] (a h : Block N) : Block N :=
  fun i => ∑ r : ZMod N, a r * h (i-r)
def rev (N : ℕ) (a : Block N) : Block N := fun i => a (-i)
noncomputable def dot (N : ℕ) [NeZero N] (a b : Block N) : ZMod 2 := ∑ i, a i * b i
noncomputable def pairing (N : ℕ) [NeZero N] (z w : Word N) : ZMod 2 := dot N z.1 w.1 + dot N z.2 w.2
def J (N : ℕ) (z : Word N) : Word N := (rev N z.2, rev N z.1)
noncomputable def boundary (N : ℕ) [NeZero N] (a b h : Block N) : Word N := (conv N a h, conv N b h)
noncomputable def syndrome (N : ℕ) [NeZero N] (a b : Block N) (z : Word N) : Block N := fun i => conv N b z.1 i + conv N a z.2 i
noncomputable def delta (N : ℕ) (j : ZMod N) : Block N := fun i => if i=j then 1 else 0
noncomputable def weight (N : ℕ) [NeZero N] (a : Block N) : ℕ := (Finset.univ.filter (fun i => a i ≠ 0)).card
noncomputable def wordWeight (N : ℕ) [NeZero N] (z : Word N) : ℕ := weight N z.1 + weight N z.2
end M6.Physical
