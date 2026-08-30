import ArchonPhysics.ActualThreeSiteIteratedA2OuterAlgebraicCertificate

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterAlgebraicCertificate
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet

noncomputable section

example (fixed : Lattice.PositiveMassConfig 3) :
    IteratedA2PairAlgebraicRegularityCertificate fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm :=
  frozenFiberThreeSiteOuterAlgebraicRegularityCertificate fixed

example (fixed : Lattice.PositiveMassConfig 3) :
    (frozenFiberThreeSiteOuterAlgebraicRegularityCertificate fixed).jacobianPolynomial =
        frozenFiberThreeSiteOuterJacobianPolynomial fixed := rfl

example :
    IteratedA2ChannelAvoidsAcoustic .outer firstPositivePhysicalModeThree
      threeSiteSingleFrequencyOuterTerm :=
  threeSiteSingleFrequencyOuter_avoidsAcoustic

#print axioms frozenFiberThreeSite_outerVerticalJacobian_zero_forces_inverse_eq
#print axioms frozenFiberThreeSite_outerVerticalJacobian_zero_forces_polynomial_zero
#print axioms frozenFiberThreeSiteOuterJacobianPolynomial_ne_zero
#print axioms threeSiteSingleFrequencyOuter_avoidsAcoustic
#print axioms frozenFiberThreeSiteOuterAlgebraicRegularityCertificate

end

end ArchonPhysicsConsumers.Thermalization
