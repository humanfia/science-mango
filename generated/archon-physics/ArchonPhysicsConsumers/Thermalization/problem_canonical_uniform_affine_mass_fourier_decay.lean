import ArchonPhysics.CanonicalUniformAffineMassFourierDecay

/-!
# Consumer: concrete uniform affine one-mass Fourier decay

This consumer instantiates the endpoint formula and the explicit
`1 / |time|` certificate for a single canonical uniform mass coordinate.
The final example uses the centered affine mismatch `mass - 1` and constant
weight one.  It does not identify that local mismatch with an FPUT
eigenfrequency mismatch.
-/

namespace ArchonPhysicsConsumers.Thermalization.CanonicalUniformAffineMassFourierDecay

open ArchonPhysics
open ArchonPhysics.CanonicalUniformAffineMassFourierDecay

noncomputable section

example {slope intercept time : Real} (weight : Complex)
    (hfrequency : time * slope ≠ 0) :
    uniformAffineOneMassExpectation slope intercept time weight =
      (5 / 2 : Real) •
        (Complex.exp (Complex.I * ((time * intercept : Real) : Complex)) *
          ((Complex.exp
              ((Complex.I * ((time * slope : Real) : Complex)) *
                (RandomEnsemble.massUpper : Complex)) -
            Complex.exp
              ((Complex.I * ((time * slope : Real) : Complex)) *
                (RandomEnsemble.massLower : Complex))) /
            (Complex.I * ((time * slope : Real) : Complex))) * weight) :=
  uniformAffineOneMassExpectation_eq_endpoint weight hfrequency

example (site : Nat) {slope intercept time : Real} (weight : Complex)
    (hslope : slope ≠ 0) (htime : time ≠ 0) :
    norm (canonicalAffineOneMassExpectation
      site slope intercept time weight) ≤
        (5 * norm weight / abs slope) / abs time :=
  norm_canonicalAffineOneMassExpectation_le_div_abs_time
    site weight hslope htime

/-- A completely numerical certificate for the centered coordinate:
`E exp(I t (m_site - 1))` is bounded by `5 / |t|`. -/
example (site : Nat) {time : Real} (htime : time ≠ 0) :
    norm (canonicalCenteredMassFourierExpectation site time) ≤
      5 / abs time :=
  norm_canonicalCenteredMassFourierExpectation_le site htime

#print axioms uniformAffineOneMassExpectation_eq_endpoint
#print axioms norm_canonicalAffineOneMassExpectation_le_div_abs_time
#print axioms norm_canonicalCenteredMassFourierExpectation_le

end

end ArchonPhysicsConsumers.Thermalization.CanonicalUniformAffineMassFourierDecay
