import M7ActionAccepted
import M7Supports
import M7QuotientAuto

namespace M7.AffinePolynomial
noncomputable def image {N : ℕ} (A : M7.Supports.Support N) : M6.Cyclic.CycleRing N :=
  M6.Cyclic.image N (M7.Supports.polynomial A)
noncomputable def shifted {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (s : ZMod N)
    (A : M7.Supports.Support N) : M7.Supports.Support N := A.image (M7.Action.affine u s)
end M7.AffinePolynomial
