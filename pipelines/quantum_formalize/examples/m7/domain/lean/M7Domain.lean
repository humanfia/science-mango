import M7SupportsAccepted
import M6FinalDomain
namespace M7.Domain
abbrev Support (N : ℕ) := M7.Supports.Support N
noncomputable def connectivityGcd {N : ℕ} (A B : Support N) : ℕ :=
 Nat.gcd N ((M7.Supports.natSupport A ∪ M7.Supports.natSupport B).gcd id)
noncomputable def signature {N : ℕ} (A B : Support N) : M6.Cyclic.BinaryPolynomial :=
 M6.Cyclic.signature (M7.Supports.polynomial A) (M7.Supports.polynomial B) (M6.Cyclic.modulus N)
noncomputable def shift {N : ℕ} (A : Support N) (r : ZMod N) : Support N := A.image (fun i => i+r)
end M7.Domain
