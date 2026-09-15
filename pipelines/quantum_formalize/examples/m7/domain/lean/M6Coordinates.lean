import M6CyclicAccepted
import M6Physical
open scoped BigOperators
namespace M6.Coordinates
noncomputable def blockPolynomial (N : ℕ) [NeZero N] (h : M6.Physical.Block N) : M6.Cyclic.BinaryPolynomial :=
  ∑ i : Fin N, Polynomial.C (h (i.val : ZMod N)) * Polynomial.X ^ i.val
noncomputable def encode (N : ℕ) [NeZero N] (h : M6.Physical.Block N) : M6.Cyclic.CycleRing N :=
  AdjoinRoot.mk (M6.Cyclic.modulus N) (blockPolynomial N h)
noncomputable def rootPow (N : ℕ) [NeZero N] (i : ZMod N) : M6.Cyclic.CycleRing N :=
  (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ i.val
noncomputable def coefficients (N : ℕ) (p : M6.Cyclic.BinaryPolynomial) : M6.Physical.Block N := fun i => p.coeff i.val
end M6.Coordinates
