import ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing

/-!
# A complete algebraic-regularity certificate for one actual three-site A2 channel

This module packages the explicit frozen-fiber Jacobian eliminant together
with the general spectrum resultant.  The result is the project-level
certificate consumed by the algebraic bad-set and signed-closure APIs.
-/

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterAlgebraicCertificate

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing

noncomputable section

/-- For every positive frozen third mass, the concrete ordinary outer
three-site history has a complete algebraic regularity certificate. -/
def frozenFiberThreeSiteOuterAlgebraicRegularityCertificate
    (fixed : Lattice.PositiveMassConfig 3) :
    IteratedA2PairAlgebraicRegularityCertificate fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm :=
  algebraicRegularityCertificateOfJacobian
    (site₁ := (0 : Lattice.Site 3)) (site₂ := (1 : Lattice.Site 3))
    fixed .outer firstPositivePhysicalModeThree
      threeSiteSingleFrequencyOuterTerm (by decide)
      (frozenFiberThreeSiteOuterJacobianPolynomial fixed)
      (frozenFiberThreeSiteOuterJacobianPolynomial_ne_zero fixed)
      (frozenFiberThreeSite_outerVerticalJacobian_zero_forces_polynomial_zero
        fixed)

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterAlgebraicCertificate
