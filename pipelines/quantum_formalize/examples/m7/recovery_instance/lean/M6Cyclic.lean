import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
namespace M6.Cyclic
abbrev BinaryPolynomial := Polynomial (ZMod 2)
noncomputable def modulus (N : ℕ) : BinaryPolynomial := Polynomial.X ^ N + 1
noncomputable def signature (a b M : BinaryPolynomial) : BinaryPolynomial :=
  EuclideanDomain.gcd (EuclideanDomain.gcd a b) M
abbrev CycleRing (N : ℕ) := AdjoinRoot (modulus N)
noncomputable def image (N : ℕ) (a : BinaryPolynomial) : CycleRing N := AdjoinRoot.mk (modulus N) a
noncomputable def boundary (N : ℕ) (a b : BinaryPolynomial) (h : CycleRing N) : CycleRing N × CycleRing N :=
  (image N a * h, image N b * h)
noncomputable def syndrome (N : ℕ) (a b : BinaryPolynomial) (z : CycleRing N × CycleRing N) : CycleRing N :=
  image N b * z.1 + image N a * z.2
end M6.Cyclic
