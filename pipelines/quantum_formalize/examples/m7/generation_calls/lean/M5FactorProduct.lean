import M5BinaryDivisibility
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain

namespace M5.FactorProduct

noncomputable def residualFactors (P F : M5.BinaryPolynomial) : Finset M5.BinaryPolynomial :=
  (UniqueFactorizationMonoid.normalizedFactors (P / F)).toFinset

end M5.FactorProduct
