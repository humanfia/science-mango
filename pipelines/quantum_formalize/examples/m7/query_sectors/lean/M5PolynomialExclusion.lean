import M5BinaryDivisibility
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

namespace M5.PolynomialExclusion

noncomputable def residualFactors (P F : M5.BinaryPolynomial) : Finset M5.BinaryPolynomial :=
  (UniqueFactorizationMonoid.normalizedFactors (P / F)).toFinset

end M5.PolynomialExclusion
