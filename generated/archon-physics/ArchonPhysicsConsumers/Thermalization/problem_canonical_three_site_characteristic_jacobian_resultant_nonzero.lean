import ArchonPhysics.CanonicalThreeSiteCharacteristicJacobianResultantNonzero

/-!
# Consumer: the canonical reduced characteristic-Jacobian resultant is nonzero at three sites

This consumer records the exact three-site specialization for varied sites
`0,1` and an arbitrary frozen third mass.  The conclusion is polynomial
nonvanishing, together with an exact square identity and zero-set
identification.  It does not claim a uniform positive lower bound near the
affine zero hyperplane.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.CanonicalThreeSiteCharacteristicJacobianResultantNonzero

noncomputable section

example (fixed : Lattice.PositiveMassConfig 3) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) =
      -MvPolynomial.C 3 *
        (frozenFiberThreeSiteOuterJacobianPolynomial fixed) ^ 2 :=
  twoSitePositiveCharacteristicJacobianResultant_zero_one_eq_frozenFiber_sq fixed

example (fixed : Lattice.PositiveMassConfig 3) :
    twoSitePositiveCharacteristicJacobianResultant fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) ≠ 0 :=
  twoSitePositiveCharacteristicJacobianResultant_zero_one_ne_zero fixed

example (fixed : Lattice.PositiveMassConfig 3)
    (coordinates : Fin 2 → Real) :
    MvPolynomial.eval coordinates
        (twoSitePositiveCharacteristicJacobianResultant fixed
          (0 : Lattice.Site 3) (1 : Lattice.Site 3)) = 0 ↔
      MvPolynomial.eval coordinates
        (frozenFiberThreeSiteOuterJacobianPolynomial fixed) = 0 :=
  twoSitePositiveCharacteristicJacobianResultant_zero_one_eval_eq_zero_iff_frozenFiber
    fixed coordinates

end

end ArchonPhysicsConsumers.Thermalization
