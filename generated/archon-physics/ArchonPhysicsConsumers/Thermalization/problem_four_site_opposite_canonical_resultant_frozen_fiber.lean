import ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiber

/-!
# Consumer: four-site opposite canonical resultant on a frozen fiber

For varied sites `0,2`, the canonical reduced characteristic-Jacobian
resultant is a nonzero polynomial exactly when the inverse masses frozen at
sites `1,3` differ.  Its evaluated zero set may still meet the affine
varied-coordinate hypersurface displayed below.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiber

noncomputable section

example (fixed : Lattice.PositiveMassConfig 4) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) =
      MvPolynomial.C 4 *
        MvPolynomial.C
          (frozenInverseWeightOne fixed - frozenInverseWeightThree fixed) ^ 2 *
        (MvPolynomial.C
            (frozenInverseWeightOne fixed + frozenInverseWeightThree fixed) *
            MvPolynomial.X 0 -
          MvPolynomial.C
            (2 * frozenInverseWeightOne fixed *
              frozenInverseWeightThree fixed)) ^ 2 :=
  twoSitePositiveCharacteristicJacobianResultant_zero_two_eq fixed

example (fixed : Lattice.PositiveMassConfig 4)
    (hfrozen :
      frozenInverseWeightOne fixed ≠ frozenInverseWeightThree fixed) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) ≠ 0 :=
  twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero fixed hfrozen

example (fixed : Lattice.PositiveMassConfig 4) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) ≠ 0 ↔
      frozenInverseWeightOne fixed ≠ frozenInverseWeightThree fixed :=
  twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_iff fixed

example (fixed : Lattice.PositiveMassConfig 4) (coordinates : Fin 2 → Real) :
    MvPolynomial.eval coordinates
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 4) (2 : Lattice.Site 4)) = 0 ↔
      frozenInverseWeightOne fixed = frozenInverseWeightThree fixed ∨
        (frozenInverseWeightOne fixed + frozenInverseWeightThree fixed) *
            coordinates 0 =
          2 * frozenInverseWeightOne fixed *
            frozenInverseWeightThree fixed :=
  twoSitePositiveCharacteristicJacobianResultant_zero_two_eval_eq_zero_iff
    fixed coordinates

end

end ArchonPhysicsConsumers.Thermalization
