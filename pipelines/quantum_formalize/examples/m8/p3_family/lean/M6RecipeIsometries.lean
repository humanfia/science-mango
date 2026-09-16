import M6Flatten
import M6Spaces
import Mathlib.Algebra.Group.Units.Equiv

namespace M6.RecipeIsometries

abbrev Block (N : ℕ) := M6.Physical.Block N
abbrev Word (N : ℕ) := M6.Physical.Word N

def shift (N : ℕ) (r : ZMod N) (a : Block N) : Block N := fun i => a (i-r)
def multiply (N : ℕ) (u : (ZMod N)ˣ) (a : Block N) : Block N :=
  fun i => a ((↑(u⁻¹) : ZMod N) * i)
def translateWord (N : ℕ) (r s : ZMod N) (z : Word N) : Word N :=
  (shift N r z.1, shift N s z.2)
def multiplyWord (N : ℕ) (u : (ZMod N)ˣ) (z : Word N) : Word N :=
  (multiply N u z.1, multiply N u z.2)
def exchange (N : ℕ) (z : Word N) : Word N := (z.2,z.1)

noncomputable def lift (N : ℕ) [NeZero N] (P : Word N → Word N)
    (v : M6.Pinned.Vector (2*N)) : M6.Pinned.Vector (2*N) :=
  M6.Flatten.flatten N (P (M6.Flatten.unflatten N v))
noncomputable def translate (N : ℕ) [NeZero N] (r s : ZMod N) :=
  lift N (translateWord N r s)
noncomputable def multiplier (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :=
  lift N (multiplyWord N u)
noncomputable def blockExchange (N : ℕ) [NeZero N] := lift N (exchange N)

end M6.RecipeIsometries
