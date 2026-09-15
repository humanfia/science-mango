import M7QuotientAutoAccepted
import M7SignatureIdealAccepted
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Polynomial.Monic
namespace M7.SignatureTau
noncomputable def equiv {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    M6.Cyclic.CycleRing N ≃+* M6.Cyclic.CycleRing N :=
  { M7.QuotientAuto.substitution u with
    invFun := M7.QuotientAuto.substitution (u⁻¹)
    left_inv := M7.QuotientAuto.substitution_left_inverse N u
    right_inv := M7.QuotientAuto.substitution_right_inverse N u }
noncomputable def substituted {N : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (F : M6.Cyclic.BinaryPolynomial) : M6.Cyclic.BinaryPolynomial :=
  F.comp (Polynomial.X ^ (u : ZMod N).val)
/-- The canonical reduced polynomial representative used by the source algorithm. -/
noncomputable def reduced {N : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (F : M6.Cyclic.BinaryPolynomial) : M6.Cyclic.BinaryPolynomial :=
  (substituted u F) %ₘ (M6.Cyclic.modulus N)
/-- Unreduced computationally equivalent gcd, with equivalence a proof obligation below. -/
noncomputable def tau {N : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (F : M6.Cyclic.BinaryPolynomial) : M6.Cyclic.BinaryPolynomial :=
  EuclideanDomain.gcd (substituted u F) (M6.Cyclic.modulus N)
/-- Literal source ordering and reduced representative: gcd(M, sigma_u(F)). -/
noncomputable def sourceTau {N : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (F : M6.Cyclic.BinaryPolynomial) : M6.Cyclic.BinaryPolynomial :=
  EuclideanDomain.gcd (M6.Cyclic.modulus N) (reduced u F)
end M7.SignatureTau
