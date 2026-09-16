import M8P4FamilyAccepted

namespace M8.P4Gcd
noncomputable def oddCofactor (m : ℕ) : M6.Cyclic.BinaryPolynomial :=
  (Finset.range (2*m+1)).sum (fun i => Polynomial.X^(2*i))
end M8.P4Gcd
